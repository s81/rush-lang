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

/* Dead cycles: each drop reads its peer, allocates, and asks for a collection. */
typedef struct node { struct node *peer; int64_t magic; } node;
static long cycle_drops, bad_peers, reentered;
static void node_drop(void *p) {
    node *n = (node *)p;
    if (n->peer->magic != 42) bad_peers++;
    cycle_drops++;
    rush_gc_alloc(sizeof(pair), NULL);
    int64_t before = rush_gc_live_objects();
    rush_gc_collect(); /* must not re-enter the running sweep */
    if (rush_gc_live_objects() != before) reentered++;
}

static void make_cycles(void) {
    for (int i = 0; i < 1000; i++) {
        node *a = (node *)rush_gc_alloc(sizeof(node), node_drop);
        node *b = (node *)rush_gc_alloc(sizeof(node), node_drop);
        a->peer = b;
        b->peer = a;
        a->magic = b->magic = 42;
    }
}

static int status = 1;

static void body(void) {
    int64_t sum = churn(100);
    if (sum < 0) return;
    if (sum != 45 + 1000) {
        printf("bad sum %lld\n", (long long)sum);
        return;
    }
    if (drops < 99997 || drops > 100000) {
        printf("drops %ld (expected about 100000)\n", drops);
        return;
    }
    /* Interior pointers keep objects alive too. */
    pair *p = (pair *)rush_gc_alloc(sizeof(pair), count_inner_drop);
    int64_t *inner = &p->b;
    p = NULL;
    rush_gc_collect();
    if (inner_drops != 0) {
        printf("interior pointer lost the object\n");
        return;
    }
    *inner = 7;
    /* Strings with capacity are freed by drop; literals are not. */
    rush_str lit = rush_str_lit("abc", 3);
    rush_str owned = rush_str_clone(&lit);
    if (!rush_str_eq(lit, owned) || owned.cap == 0) return;
    rush_str both = rush_str_concat(&lit, &owned);
    if (both.len != 6) return;
    rush_str_drop(&both);
    rush_str_drop(&owned);
    rush_str_drop(&lit);
    if (rush_add_i64_checked(1, 2) != 3 || rush_mul_i64_checked(-3, 4) != -12) return;
    make_cycles();
    rush_gc_collect();
    if (cycle_drops < 1990 || bad_peers != 0 || reentered != 0) {
        printf("cycle drops %ld, bad peers %ld, reentered %ld\n", cycle_drops, bad_peers, reentered);
        return;
    }
    puts("gc ok");
    status = 0;
}

int main(int argc, char **argv) {
    rush_rt_run(argc, argv, body);
    return status;
}
