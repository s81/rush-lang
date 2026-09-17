#include "rush_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void rush_rt_init(int argc, char **argv) {
    (void)argc;
    (void)argv;
}

void rush_panic(const char *msg) {
    fprintf(stderr, "panic: %s\n", msg);
    fflush(stderr);
    abort();
}

void rush_unreachable(void) {
    rush_panic("entered unreachable code");
}

rush_str rush_str_lit(const char *s, size_t len) {
    rush_str r;
    r.ptr = (const uint8_t *)s;
    r.len = len;
    return r;
}

bool rush_str_eq(rush_str a, rush_str b) {
    return a.len == b.len && memcmp(a.ptr, b.ptr, a.len) == 0;
}

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

rush_unit rush_puts(rush_str s) {
    fwrite(s.ptr, 1, s.len, stdout);
    fputc('\n', stdout);
    return RUSH_UNIT;
}

rush_unit rush_print(rush_str s) {
    fwrite(s.ptr, 1, s.len, stdout);
    return RUSH_UNIT;
}

/* ponytail: these allocate and never free; Plan 3 makes String owned and dropped. */
static rush_str rush_str_own(const char *buf, size_t len) {
    uint8_t *p = (uint8_t *)malloc(len ? len : 1);
    if (!p) rush_panic("out of memory");
    memcpy(p, buf, len);
    rush_str r;
    r.ptr = p;
    r.len = len;
    return r;
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

rush_str rush_str_concat(rush_str a, rush_str b) {
    size_t len = a.len + b.len;
    uint8_t *p = (uint8_t *)malloc(len ? len : 1);
    if (!p) rush_panic("out of memory");
    memcpy(p, a.ptr, a.len);
    memcpy(p + a.len, b.ptr, b.len);
    rush_str r;
    r.ptr = p;
    r.len = len;
    return r;
}
