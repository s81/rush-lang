/* Standalone check of the collector: build with the runtime and run. Exit code 0 on success. */
#include "rush_rt.h"
#include <stdio.h>
#include <string.h>

static long drops;
static long inner_drops;
static void count_drop(void *p) { (void)p; drops++; }
static void count_inner_drop(void *p) { (void)p; inner_drops++; }

typedef struct { int64_t a; int64_t b; } pair;

/* Keeps `keep` live on this frame while churning through garbage. */
static int64_t churn(int64_t keep_n) {
    pair *keep[10];
    int64_t sum = 0;
    for (int i = 0; i < 10; i++) {
        keep[i] = (pair *)rush_gc_alloc(sizeof(pair), count_drop);
        keep[i]->a = i;
        keep[i]->b = keep_n;
    }
    for (int i = 0; i < 100000; i++) {
        pair *junk = (pair *)rush_gc_alloc(sizeof(pair), count_drop);
        junk->a = i;
    }
    rush_gc_collect();
    /* Conservative scanning may keep a couple of stale stack slots alive. */
    if (rush_gc_live_objects() < 10 || rush_gc_live_objects() > 13) {
        printf("live after collect: %lld (expected 10..13)\n", (long long)rush_gc_live_objects());
        return -1;
    }
    for (int i = 0; i < 10; i++) sum += keep[i]->a + keep[i]->b;
    return sum;
}

int main(int argc, char **argv) {
    rush_rt_init(argc, argv);
    int64_t sum = churn(100);
    if (sum < 0) return 1;
    if (sum != 45 + 1000) {
        printf("bad sum %lld\n", (long long)sum);
        return 1;
    }
    if (drops < 99997 || drops > 100000) {
        printf("drops %ld (expected about 100000)\n", drops);
        return 1;
    }
    /* Interior pointers keep objects alive too. */
    pair *p = (pair *)rush_gc_alloc(sizeof(pair), count_inner_drop);
    int64_t *inner = &p->b;
    p = NULL;
    rush_gc_collect();
    if (inner_drops != 0) {
        printf("interior pointer lost the object\n");
        return 1;
    }
    *inner = 7;
    /* Strings with capacity are freed by drop; literals are not. */
    rush_str lit = rush_str_lit("abc", 3);
    rush_str owned = rush_str_clone(&lit);
    if (!rush_str_eq(lit, owned) || owned.cap == 0) return 1;
    rush_str_drop(&owned);
    rush_str_drop(&lit);
    if (rush_add_i64_checked(1, 2) != 3 || rush_mul_i64_checked(-3, 4) != -12) return 1;
    puts("gc ok");
    return 0;
}
