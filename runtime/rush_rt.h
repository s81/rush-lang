#ifndef RUSH_RT_H
#define RUSH_RT_H
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct { char _; } rush_unit;
#define RUSH_UNIT ((rush_unit){0})

/* Immutable UTF-8 string view. Plan 3 adds ownership and drop. */
typedef struct { const uint8_t *ptr; size_t len; } rush_str;

void rush_rt_init(int argc, char **argv);
void rush_panic(const char *msg);
void rush_unreachable(void);
rush_str rush_str_lit(const char *s, size_t len);
bool rush_str_eq(rush_str a, rush_str b);
int64_t rush_div_i64(int64_t a, int64_t b);
int64_t rush_rem_i64(int64_t a, int64_t b);

/* Primitives declared in std/prelude.rush as extern "C". */
rush_unit rush_puts(rush_str s);
rush_unit rush_print(rush_str s);
rush_str rush_int_to_s(int64_t v);
rush_str rush_float_to_s(double v);
rush_str rush_bool_to_s(bool v);
rush_str rush_str_concat(rush_str a, rush_str b);

#endif
