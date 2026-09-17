#ifndef RUSH_RT_H
#define RUSH_RT_H
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct { char _; } rush_unit;
#define RUSH_UNIT ((rush_unit){0})

/* UTF-8 string. cap == 0 means static or borrowed storage that is never freed. */
typedef struct { uint8_t *ptr; size_t len; size_t cap; } rush_str;

void rush_rt_init(int argc, char **argv);
void rush_panic(const char *msg);
void rush_unreachable(void);
rush_str rush_str_lit(const char *s, size_t len);
void rush_str_drop(rush_str *s);
rush_str rush_str_clone(const rush_str *s);
bool rush_str_eq(rush_str a, rush_str b);
int64_t rush_div_i64(int64_t a, int64_t b);
int64_t rush_rem_i64(int64_t a, int64_t b);
int64_t rush_add_i64_checked(int64_t a, int64_t b);
int64_t rush_sub_i64_checked(int64_t a, int64_t b);
int64_t rush_mul_i64_checked(int64_t a, int64_t b);

/* Conservative mark-sweep collector. */
typedef void (*rush_drop_fn)(void *);
void *rush_gc_alloc(size_t size, rush_drop_fn drop);
void rush_gc_collect(void);
int64_t rush_gc_live_objects(void);

/* Primitives declared in std/prelude.rush as extern "C". */
rush_unit rush_puts(rush_str s);
rush_unit rush_print(rush_str s);
rush_str rush_int_to_s(int64_t v);
rush_str rush_float_to_s(double v);
rush_str rush_bool_to_s(bool v);
rush_str rush_str_concat(rush_str a, rush_str b);
rush_unit rush_gc_collect_rt(rush_unit u);
int64_t rush_gc_live_objects_rt(rush_unit u);

#endif
