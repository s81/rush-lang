#include "rush_rt.h"
#include <math.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- basics ---------- */

static uintptr_t rush_stack_base;

void rush_rt_init(int argc, char **argv) {
    (void)argc;
    (void)argv;
}

int rush_rt_run(int argc, char **argv, void (*entry)(int, char **)) {
    volatile uintptr_t marker = 0;
    rush_stack_base = (uintptr_t)&marker;
    entry(argc, argv);
    /* stdout is buffered, so a write error may only surface at the final flush. */
    if (fflush(stdout) != 0) rush_panic("failed to flush stdout");
    return 0;
}

void rush_panic(const char *msg) {
    /* A panic aborts without flushing stdio, so flush what the program already printed. */
    (void)fflush(stdout);
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

/* Symbols are static C strings; the returned string borrows the storage (cap 0). */
rush_str rush_sym_to_s(const char *s) {
    rush_str r;
    r.ptr = (uint8_t *)s;
    r.len = strlen(s);
    r.cap = 0;
    return r;
}

rush_str rush_str_concat(const rush_str *a, const rush_str *b) {
    size_t len = a->len + b->len;
    uint8_t *p = (uint8_t *)malloc(len ? len : 1);
    if (!p) rush_panic("out of memory");
    memcpy(p, a->ptr, a->len);
    memcpy(p + a->len, b->ptr, b->len);
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

/* Unsigned arithmetic has defined wraparound; the conversion back to int64_t is implementation
   defined in C99 but is two's complement on every target Rush supports. */
int64_t rush_add_i64_wrapping(int64_t a, int64_t b) {
    return (int64_t)((uint64_t)a + (uint64_t)b);
}

int64_t rush_sub_i64_wrapping(int64_t a, int64_t b) {
    return (int64_t)((uint64_t)a - (uint64_t)b);
}

int64_t rush_mul_i64_wrapping(int64_t a, int64_t b) {
    return (int64_t)((uint64_t)a * (uint64_t)b);
}

/* ---------- IO ---------- */

static void rush_stdout_write(const void *p, size_t n) {
    if (n != 0 && fwrite(p, 1, n, stdout) != n) rush_panic("failed to write to stdout");
}

rush_unit rush_puts(const rush_str *s) {
    rush_stdout_write(s->ptr, s->len);
    if (fputc('\n', stdout) == EOF) rush_panic("failed to write to stdout");
    return RUSH_UNIT;
}

rush_unit rush_print(const rush_str *s) {
    rush_stdout_write(s->ptr, s->len);
    return RUSH_UNIT;
}

rush_str rush_int_to_s(int64_t v) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%lld", (long long)v);
    return rush_str_own(buf, (size_t)n);
}

/* Shortest `%g` form that parses back to exactly `v`, then Ruby-shaped: a decimal point is
   always present and exponents have no leading zeros (`1.0e+6`, not `1e+06`). */
static size_t rush_float_normalize(const char *in, size_t n, char *out) {
    const char *e = strchr(in, 'e');
    if (!e) e = strchr(in, 'E');
    size_t mantissa = e ? (size_t)(e - in) : n;
    size_t o = 0;
    memcpy(out, in, mantissa);
    o = mantissa;
    if (!memchr(in, '.', mantissa)) {
        out[o++] = '.';
        out[o++] = '0';
    }
    if (e) {
        out[o++] = 'e';
        const char *p = e + 1;
        char sign = '+';
        if (*p == '+' || *p == '-') sign = *p++;
        while (*p == '0' && p[1] != '\0') p++;
        out[o++] = sign;
        size_t digits = strlen(p);
        memcpy(out + o, p, digits);
        o += digits;
    }
    out[o] = '\0';
    return o;
}

rush_str rush_float_to_s(double v) {
    if (isnan(v)) return rush_str_lit("NaN", 3);
    if (isinf(v)) return v < 0 ? rush_str_lit("-Infinity", 9) : rush_str_lit("Infinity", 8);
    char buf[64];
    int n = 0;
    for (int precision = 1; precision <= 17; precision++) {
        n = snprintf(buf, sizeof buf, "%.*g", precision, v);
        if (n < 0 || (size_t)n >= sizeof buf) break;
        char *end = NULL;
        double back = strtod(buf, &end);
        if (end && *end == '\0' && back == v) break;
    }
    if (n < 0 || (size_t)n >= sizeof buf) n = snprintf(buf, sizeof buf, "%.17g", v);
    char out[96];
    size_t len = rush_float_normalize(buf, (size_t)n, out);
    return rush_str_own(out, len);
}

rush_str rush_bool_to_s(bool v) {
    return v ? rush_str_lit("true", 4) : rush_str_lit("false", 5);
}

/* ---------- garbage collector ----------
 * Conservative, non-moving, stop-the-world mark-sweep. Every object has a header followed by
 * the payload. Roots are the C stack (registers spilled with setjmp), registered global-root
 * callbacks, and the bodies of reachable GC objects, scanned word by word.
 * A word is a pointer if it lands inside any live object (binary search over sorted ranges).
 *
 * Only GC payloads are traced. If a GC payload points into malloc-backed storage (for example
 * a string buffer or a C-side registry), that storage is not scanned for further GC handles:
 * every live handle must also be reachable from a stack frame, a registered global root, or a
 * GC payload. Runtime structures that hold `Gc` handles across collections must register a
 * root scan with `rush_gc_register_roots`.
 */

typedef struct rush_gc_hdr {
    size_t size;                 /* payload bytes */
    rush_drop_fn drop;
    struct rush_gc_hdr *next;
    uint8_t mark;
    uint8_t pad[3];
    int32_t borrows;             /* 0 free, n > 0 shared borrows, -1 mutably borrowed */
} rush_gc_hdr;

static rush_gc_hdr *gc_objects;
static size_t gc_count;
static size_t gc_bytes_since;
static size_t gc_threshold = 1u << 20;

static rush_gc_hdr **gc_sorted;
static size_t gc_sorted_len;

static rush_gc_hdr **gc_mark_stack;
static size_t gc_mark_len, gc_mark_cap;

static rush_gc_root_fn *gc_roots;
static size_t gc_roots_len, gc_roots_cap;

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

void rush_gc_mark_ptr(const void *p) {
    if (p) gc_mark_word((uintptr_t)p);
}

void rush_gc_mark_range(const void *base, size_t len) {
    if (base && len) gc_scan_range((uintptr_t)base, (uintptr_t)base + len);
}

void rush_gc_register_roots(rush_gc_root_fn scan) {
    if (!scan) return;
    for (size_t i = 0; i < gc_roots_len; i++)
        if (gc_roots[i] == scan) return;
    if (gc_roots_len == gc_roots_cap) {
        gc_roots_cap = gc_roots_cap ? gc_roots_cap * 2 : 8;
        gc_roots = (rush_gc_root_fn *)realloc(gc_roots, gc_roots_cap * sizeof *gc_roots);
        if (!gc_roots) rush_panic("out of memory");
    }
    gc_roots[gc_roots_len++] = scan;
}

void rush_gc_unregister_roots(rush_gc_root_fn scan) {
    for (size_t i = 0; i < gc_roots_len; i++) {
        if (gc_roots[i] != scan) continue;
        memmove(&gc_roots[i], &gc_roots[i + 1], (gc_roots_len - i - 1) * sizeof *gc_roots);
        gc_roots_len--;
        return;
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
    for (size_t i = 0; i < gc_roots_len; i++)
        gc_roots[i]();
    while (gc_mark_len) {
        rush_gc_hdr *h = gc_mark_stack[--gc_mark_len];
        uintptr_t start = (uintptr_t)(h + 1);
        gc_scan_range(start, start + h->size);
    }
    /* Sweep: unlink every dead object, then run all drops, then free. A drop may read other
       dead objects (a cycle), so nothing is freed until every drop has run. */
    rush_gc_hdr **link = &gc_objects;
    rush_gc_hdr *dead = NULL;
    size_t live_bytes = 0;
    while (*link) {
        rush_gc_hdr *h = *link;
        if (h->mark) {
            live_bytes += h->size;
            link = &h->next;
        } else {
            *link = h->next;
            h->next = dead;
            dead = h;
            gc_count--;
        }
    }
    gc_bytes_since = 0;
    gc_threshold = live_bytes * 2 > (1u << 20) ? live_bytes * 2 : (1u << 20);
    /* ponytail: a drop that stores a dead object's handle somewhere live resurrects it into a
       dangling handle; finalizer resurrection needs a second mark pass if it ever matters. */
    for (rush_gc_hdr *h = dead; h; h = h->next)
        if (h->drop) h->drop(h + 1);
    while (dead) {
        rush_gc_hdr *next = dead->next;
        free(dead);
        dead = next;
    }
}

/* Set while a collection runs, so drops that allocate cannot re-enter the collector. */
static int gc_running;

void rush_gc_collect(void) {
    if (gc_running) return;
    gc_running = 1;
    jmp_buf regs;
    volatile uintptr_t top;
#if (defined(__GNUC__) || defined(__clang__)) && !defined(__TINYC__)
    /* glibc mangles the frame pointer inside jmp_buf; this saves every callee-saved register
       unmangled in this frame. */
    __builtin_unwind_init();
#endif
    setjmp(regs); /* spill callee-saved registers onto this frame */
    top = (uintptr_t)&regs;
    gc_collect_from(top < (uintptr_t)&top ? top : (uintptr_t)&top);
    gc_running = 0;
}

void *rush_gc_alloc(size_t size, rush_drop_fn drop) {
    if (gc_bytes_since > gc_threshold) rush_gc_collect();
    rush_gc_hdr *h = (rush_gc_hdr *)malloc(sizeof *h + (size ? size : 1));
    if (!h) rush_panic("out of memory");
    h->size = size ? size : 1;
    h->drop = drop;
    h->mark = 0;
    h->borrows = 0;
    h->next = gc_objects;
    gc_objects = h;
    gc_count++;
    gc_bytes_since += h->size;
    memset(h + 1, 0, h->size);
    return h + 1;
}

void *rush_gc_borrow(void *p) {
    rush_gc_hdr *h = (rush_gc_hdr *)p - 1;
    if (h->borrows < 0) rush_panic("Gc value is mutably borrowed");
    h->borrows++;
    return p;
}

void *rush_gc_borrow_mut(void *p) {
    rush_gc_hdr *h = (rush_gc_hdr *)p - 1;
    if (h->borrows != 0) rush_panic("Gc value is already borrowed");
    h->borrows = -1;
    return p;
}

void rush_gc_release(void *p, bool mut) {
    rush_gc_hdr *h = (rush_gc_hdr *)p - 1;
    h->borrows = mut ? 0 : h->borrows - 1;
}

int64_t rush_gc_live_objects(void) {
    return (int64_t)gc_count;
}

rush_unit rush_gc_collect_now(void) {
    rush_gc_collect();
    return RUSH_UNIT;
}

int64_t rush_gc_live(void) {
    return rush_gc_live_objects();
}
