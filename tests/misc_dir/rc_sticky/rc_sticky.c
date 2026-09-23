/*
Regression tests for the sticky reference-count paths of the runtime (#14838, #15241).
*/
#include <lean/lean.h>
#include <stdio.h>

void lean_initialize_runtime_module(void);

static int g_failures = 0;

#define CHECK(c) do { \
    if (!(c)) { fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #c); g_failures++; } \
} while (0)

static int rc(lean_object * o) { return lean_internal_get_rc(o); }

#define CHECK_RC(o, expected) do { \
    int actual_ = rc(o), expected_ = (expected); \
    if (actual_ != expected_) { \
        fprintf(stderr, "%s:%d: count of %s is %#x, expected %#x\n", __FILE__, __LINE__, #o, \
                (unsigned)actual_, (unsigned)expected_); \
        g_failures++; \
    } \
} while (0)

static lean_object * leaf(int count) {
    lean_object * o = lean_alloc_ctor(0, 0, 0);
    lean_internal_set_rc(o, count);
    return o;
}

/* Frees `o` and what it owns through the ordinary deletion path, whatever its count, so that the leak
   checker reports only real leaks. */
static void release(lean_object * o) {
    lean_internal_set_rc(o, 1);
    lean_dec(o);
}

static lean_object * box1(lean_object * child) {
    lean_object * o = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(o, 0, child);
    return o;
}

/* Every count no drop may free or adjust: persistent, the band where drops stop, and the frozen range
   down to `INT_MIN`, which a single-threaded count reaches by wrapping. */
static const int g_never_freed[] = {
    0, LEAN_RC_STICKY_DROP, LEAN_RC_STICKY_DROP - 1, LEAN_RC_STICKY, LEAN_RC_STICKY - 1, INT_MIN + 1, INT_MIN,
};
#define NUM_NEVER_FREED (sizeof(g_never_freed) / sizeof(g_never_freed[0]))

static void test_drop_leaves_never_freed_counts(void) {
    for (size_t i = 0; i < NUM_NEVER_FREED; i++) {
        lean_object * o = leaf(g_never_freed[i]);
        lean_dec(o);
        CHECK_RC(o, g_never_freed[i]);
        release(o);
    }
}

/* Freeing a parent drops its children through the deletion cascade rather than `lean_dec_ref` (#15241). */
static void test_cascade_leaves_never_freed_counts(void) {
    for (size_t i = 0; i < NUM_NEVER_FREED; i++) {
        lean_object * child = leaf(g_never_freed[i]);
        lean_dec(box1(child));
        CHECK_RC(child, g_never_freed[i]);
        release(child);
    }
    lean_object * shared = leaf(-2);
    lean_dec(box1(shared));
    CHECK_RC(shared, -1);
    lean_dec(shared);
}

/* Counts no increment may adjust: persistent, and frozen ones. */
static const int g_never_incremented[] = {0, LEAN_RC_STICKY, LEAN_RC_STICKY - 1, INT_MIN + 1, INT_MIN};

static void test_inc_leaves_frozen_counts(void) {
    for (size_t i = 0; i < sizeof(g_never_incremented) / sizeof(g_never_incremented[0]); i++) {
        lean_object * o = leaf(g_never_incremented[i]);
        lean_inc(o);
        lean_inc_n(o, LEAN_RC_INC_MAX);
        lean_inc_n(o, LEAN_RC_INC_MAX + 1);
        CHECK_RC(o, g_never_incremented[i]);
        release(o);
    }
}

int main(void) {
    lean_initialize_runtime_module();
    test_drop_leaves_never_freed_counts();
    test_cascade_leaves_never_freed_counts();
    test_inc_leaves_frozen_counts();
    if (g_failures != 0) {
        fprintf(stderr, "%d check(s) failed\n", g_failures);
        return 1;
    }
    return 0;
}
