#include "rush_rt.h"
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- basics ---------- */

static uintptr_t rush_stack_base;

void rush_rt_init(int argc, char **argv) {
    volatile uintptr_t marker = 0;
    (void)argc;
    (void)argv;
    rush_stack_base = (uintptr_t)&marker;
}

void rush_panic(const char *msg) {
    fprintf(stderr, "panic: %s\n", msg);
    fflush(stderr);
    abort();
}

void rush_unreachable(void) {
    rush_panic("entered unreachable code");
}

/* ---------- strings ---------- */

rush_str rush_str_lit(const char *s, size_t len) {
    rush_str r;
    r.ptr = (uint8_t *)s;
    r.len = len;
    r.cap = 0;
    return r;
}

static rush_str rush_str_own(const char *buf, size_t len) {
    uint8_t *p = (uint8_t *)malloc(len ? len : 1);
    if (!p) rush_panic("out of memory");
    memcpy(p, buf, len);
    rush_str r;
    r.ptr = p;
    r.len = len;
    r.cap = len ? len : 1;
    return r;
}

void rush_str_drop(rush_str *s) {
    if (s->cap) {
        free(s->ptr);
        s->ptr = NULL;
        s->len = 0;
        s->cap = 0;
    }
}

rush_str rush_str_clone(const rush_str *s) {
    return rush_str_own((const char *)s->ptr, s->len);
}

bool rush_str_eq(rush_str a, rush_str b) {
    return a.len == b.len && memcmp(a.ptr, b.ptr, a.len) == 0;
}

rush_str rush_str_concat(rush_str a, rush_str b) {
    size_t len = a.len + b.len;
    uint8_t *p = (uint8_t *)malloc(len ? len : 1);
    if (!p) rush_panic("out of memory");
    memcpy(p, a.ptr, a.len);
    memcpy(p + a.len, b.ptr, b.len);
    rush_str r;
    r.ptr = p;
    r.len = len;
    r.cap = len ? len : 1;
    return r;
}

/* ---------- integers ---------- */

int64_t rush_div_i64(int64_t a, int64_t b) {
    if (b == 0) rush_panic("division by zero");
    if (a == INT64_MIN && b == -1) rush_panic("integer overflow in division");
    return a / b;
}

int64_t rush_rem_i64(int64_t a, int64_t b) {
    if (b == 0) rush_panic("remainder by zero");
    if (a == INT64_MIN && b == -1) return 0;
    return a % b;
}

int64_t rush_add_i64_checked(int64_t a, int64_t b) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) rush_panic("integer overflow in addition");
    return a + b;
}

int64_t rush_sub_i64_checked(int64_t a, int64_t b) {
    if ((b < 0 && a > INT64_MAX + b) || (b > 0 && a < INT64_MIN + b)) rush_panic("integer overflow in subtraction");
    return a - b;
}

int64_t rush_mul_i64_checked(int64_t a, int64_t b) {
    if (a == 0 || b == 0) return 0;
    if (a == -1) {
        if (b == INT64_MIN) rush_panic("integer overflow in multiplication");
        return -b;
    }
    if (b == -1) {
        if (a == INT64_MIN) rush_panic("integer overflow in multiplication");
        return -a;
    }
    int64_t r = (int64_t)((uint64_t)a * (uint64_t)b);
    if (r / b != a) rush_panic("integer overflow in multiplication");
    return r;
}

/* ---------- IO ---------- */

rush_unit rush_puts(rush_str s) {
    fwrite(s.ptr, 1, s.len, stdout);
    fputc('\n', stdout);
    return RUSH_UNIT;
}

rush_unit rush_print(rush_str s) {
    fwrite(s.ptr, 1, s.len, stdout);
    return RUSH_UNIT;
}

rush_str rush_int_to_s(int64_t v) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%lld", (long long)v);
    return rush_str_own(buf, (size_t)n);
}

rush_str rush_float_to_s(double v) {
    char buf[64];
    int n = snprintf(buf, sizeof buf, "%.15g", v);
    /* Print whole floats as `2.0` like Ruby, not `2`. */
    if (strspn(buf, "-0123456789") == (size_t)n) {
        buf[n++] = '.';
        buf[n++] = '0';
        buf[n] = 0;
    }
    return rush_str_own(buf, (size_t)n);
}

rush_str rush_bool_to_s(bool v) {
    return v ? rush_str_lit("true", 4) : rush_str_lit("false", 5);
}

/* ---------- garbage collector ----------
 * Conservative, non-moving, stop-the-world mark-sweep. Every object has a header followed by
 * the payload. Roots are the C stack (registers spilled with setjmp) scanned word by word.
 * A word is a pointer if it lands inside any live object (binary search over sorted ranges).
 */

typedef struct rush_gc_hdr {
    size_t size;                 /* payload bytes */
    rush_drop_fn drop;
    struct rush_gc_hdr *next;
    uint8_t mark;
    uint8_t pad[7];
} rush_gc_hdr;

static rush_gc_hdr *gc_objects;
static size_t gc_count;
static size_t gc_bytes_since;
static size_t gc_threshold = 1u << 20;

static rush_gc_hdr **gc_sorted;
static size_t gc_sorted_len;

static rush_gc_hdr **gc_mark_stack;
static size_t gc_mark_len, gc_mark_cap;

static int gc_cmp(const void *a, const void *b) {
    uintptr_t x = (uintptr_t)*(rush_gc_hdr *const *)a;
    uintptr_t y = (uintptr_t)*(rush_gc_hdr *const *)b;
    return x < y ? -1 : x > y;
}

static rush_gc_hdr *gc_find(uintptr_t word) {
    size_t lo = 0, hi = gc_sorted_len;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        rush_gc_hdr *h = gc_sorted[mid];
        uintptr_t start = (uintptr_t)(h + 1);
        uintptr_t end = start + h->size;
        if (word < start) hi = mid;
        else if (word >= end) lo = mid + 1;
        else return h;
    }
    return NULL;
}

static void gc_mark_word(uintptr_t word) {
    rush_gc_hdr *h = gc_find(word);
    if (!h || h->mark) return;
    h->mark = 1;
    if (gc_mark_len == gc_mark_cap) {
        gc_mark_cap = gc_mark_cap ? gc_mark_cap * 2 : 1024;
        gc_mark_stack = (rush_gc_hdr **)realloc(gc_mark_stack, gc_mark_cap * sizeof *gc_mark_stack);
        if (!gc_mark_stack) rush_panic("out of memory");
    }
    gc_mark_stack[gc_mark_len++] = h;
}

static void gc_scan_range(uintptr_t lo, uintptr_t hi) {
    lo &= ~(uintptr_t)(sizeof(uintptr_t) - 1);
    for (uintptr_t p = lo; p + sizeof(uintptr_t) <= hi; p += sizeof(uintptr_t)) {
        uintptr_t w;
        memcpy(&w, (const void *)p, sizeof w);
        gc_mark_word(w);
    }
}

static void gc_collect_from(uintptr_t stack_top) {
    /* Sorted index of objects for pointer identification. */
    gc_sorted = (rush_gc_hdr **)realloc(gc_sorted, (gc_count ? gc_count : 1) * sizeof *gc_sorted);
    if (!gc_sorted) rush_panic("out of memory");
    gc_sorted_len = 0;
    for (rush_gc_hdr *h = gc_objects; h; h = h->next) {
        h->mark = 0;
        gc_sorted[gc_sorted_len++] = h;
    }
    qsort(gc_sorted, gc_sorted_len, sizeof *gc_sorted, gc_cmp);
    /* Roots: the stack between the caller's frame and the base. Stacks grow down on every
       supported target; handle both directions anyway. */
    uintptr_t lo = stack_top < rush_stack_base ? stack_top : rush_stack_base;
    uintptr_t hi = stack_top < rush_stack_base ? rush_stack_base : stack_top;
    gc_mark_len = 0;
    gc_scan_range(lo, hi + sizeof(uintptr_t));
    while (gc_mark_len) {
        rush_gc_hdr *h = gc_mark_stack[--gc_mark_len];
        uintptr_t start = (uintptr_t)(h + 1);
        gc_scan_range(start, start + h->size);
    }
    /* Sweep. */
    rush_gc_hdr **link = &gc_objects;
    size_t live_bytes = 0;
    while (*link) {
        rush_gc_hdr *h = *link;
        if (h->mark) {
            live_bytes += h->size;
            link = &h->next;
        } else {
            *link = h->next;
            if (h->drop) h->drop(h + 1);
            free(h);
            gc_count--;
        }
    }
    gc_bytes_since = 0;
    gc_threshold = live_bytes * 2 > (1u << 20) ? live_bytes * 2 : (1u << 20);
}

void rush_gc_collect(void) {
    jmp_buf regs;
    volatile uintptr_t top;
    setjmp(regs); /* spill callee-saved registers onto this frame */
    top = (uintptr_t)&regs;
    gc_collect_from(top < (uintptr_t)&top ? top : (uintptr_t)&top);
}

void *rush_gc_alloc(size_t size, rush_drop_fn drop) {
    if (gc_bytes_since > gc_threshold) rush_gc_collect();
    rush_gc_hdr *h = (rush_gc_hdr *)malloc(sizeof *h + (size ? size : 1));
    if (!h) rush_panic("out of memory");
    h->size = size ? size : 1;
    h->drop = drop;
    h->mark = 0;
    h->next = gc_objects;
    gc_objects = h;
    gc_count++;
    gc_bytes_since += h->size;
    memset(h + 1, 0, h->size);
    return h + 1;
}

int64_t rush_gc_live_objects(void) {
    return (int64_t)gc_count;
}

rush_unit rush_gc_collect_rt(rush_unit u) {
    (void)u;
    rush_gc_collect();
    return RUSH_UNIT;
}

int64_t rush_gc_live_objects_rt(rush_unit u) {
    (void)u;
    return rush_gc_live_objects();
}
