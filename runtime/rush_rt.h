#ifndef RUSH_RT_H
#define RUSH_RT_H
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct { char _; } rush_unit;
#define RUSH_UNIT ((rush_unit){0})

/* A function value: a code pointer, followed in memory by its environment. The code takes the
   value itself first, then the arguments, and is cast to its real type at each call. */
typedef struct rush_fn { void (*code)(void); } rush_fn;

/* UTF-8 string. cap == 0 means static or borrowed storage that is never freed. */
typedef struct { uint8_t *ptr; size_t len; size_t cap; } rush_str;

void rush_rt_init(int argc, char **argv);
/* Records the GC stack base in its own frame, then runs `entry(argc, argv)`. Every frame the
   program creates is below this one, so the collector scans all of them. */
int rush_rt_run(int argc, char **argv, void (*entry)(int, char **));
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
/* Release-build arithmetic: wrapping two's complement, without C signed-overflow UB. */
int64_t rush_add_i64_wrapping(int64_t a, int64_t b);
int64_t rush_sub_i64_wrapping(int64_t a, int64_t b);
int64_t rush_mul_i64_wrapping(int64_t a, int64_t b);

/* Conservative mark-sweep collector. */
typedef void (*rush_drop_fn)(void *);
void *rush_gc_alloc(size_t size, rush_drop_fn drop);
void rush_gc_collect(void);
int64_t rush_gc_live_objects(void);
/* Runtime borrow flags of a Gc payload `p`: a conflicting borrow panics. */
void *rush_gc_borrow(void *p);
void *rush_gc_borrow_mut(void *p);
void rush_gc_release(void *p, bool mut);
/* Global roots live outside the C stack. Register a function that calls rush_gc_mark_ptr for
   each live global `Gc` handle (or rush_gc_mark_range for an array of them); it runs during
   every collection. Unregister before the storage it reads goes away. */
typedef void (*rush_gc_root_fn)(void);
void rush_gc_register_roots(rush_gc_root_fn scan);
void rush_gc_unregister_roots(rush_gc_root_fn scan);
void rush_gc_mark_ptr(const void *p);
void rush_gc_mark_range(const void *base, size_t len);

/* Primitives declared in std/prelude.rush as extern "C". */
rush_unit rush_puts(const rush_str *s);
rush_unit rush_print(const rush_str *s);
rush_str rush_int_to_s(int64_t v);
rush_str rush_float_to_s(double v);
rush_str rush_bool_to_s(bool v);
rush_str rush_str_concat(const rush_str *a, const rush_str *b);
rush_str rush_sym_to_s(const char *s);
rush_unit rush_gc_collect_now(void);
int64_t rush_gc_live(void);

#endif
