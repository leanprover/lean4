/*
Exercise real shared-counter updates and competing final releases through the runtime task pool.
Each worker owns its root until its final drop, including concurrent borrowed array-field retains.
Publication uses the task pool and start flag.
Run unchanged against the incumbent and generated collectors.
*/
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>

void lean_initialize_runtime_module(void);

#define CHECK(c) do { \
    if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); abort(); } \
} while (0)

enum { WORKERS = 8, ROUNDS = 32, ITERATIONS = 512 };
static atomic_bool started;
static atomic_uint finalized;
static unsigned path;
static lean_external_class * marker_class;

static void finalize(void * data) {
    CHECK(data == (void *)(uintptr_t)42);
    CHECK(atomic_fetch_add_explicit(&finalized, 1, memory_order_relaxed) == 0);
}

static void foreach(void * data, b_lean_obj_arg fn) { (void)data; (void)fn; }

static lean_obj_res worker(lean_obj_arg root, lean_obj_arg unit) {
    (void)unit;
    while (!atomic_load_explicit(&started, memory_order_acquire)) {}
    for (unsigned i = 0; i < ITERATIONS; ++i) {
        CHECK(atomic_load_explicit(&finalized, memory_order_relaxed) == 0);
        unsigned n = 1 + i % 16;
        lean_object * target = path == 3 ? lean_array_uget(root, 0) : root;
        lean_inc_ref_n(target, n);
        for (unsigned j = 0; j < n; ++j) lean_dec(target);
        if (path == 3) lean_dec(target);
    }
    CHECK(atomic_load_explicit(&finalized, memory_order_relaxed) == 0);
    lean_object * leaf = path == 0 ? root :
        path == 3 ? lean_array_uget_borrowed(root, 0) : lean_ctor_get(root, 0);
    CHECK(lean_get_external_data(leaf) == (void *)(uintptr_t)42);
    lean_dec(root);
    return lean_box(0);
}

static void shared_case(unsigned kind) {
    path = kind;
    atomic_store_explicit(&started, false, memory_order_relaxed);
    atomic_store_explicit(&finalized, 0, memory_order_relaxed);
    lean_object * leaf = lean_alloc_external(marker_class, (void *)(uintptr_t)42);
    lean_object * shared = leaf;
    if (path == 3) {
        shared = lean_alloc_array(1, 1);
        lean_array_cptr(shared)[0] = leaf;
    }
    lean_mark_mt(shared);
    lean_object * tasks[WORKERS];
    for (unsigned i = 0; i < WORKERS; ++i) {
        lean_inc(shared);
        lean_object * root = shared;
        if (path == 1 || path == 2) {
            root = lean_alloc_ctor(0, path == 1 ? 2 : 1, 0);
            lean_ctor_set(root, 0, leaf);
            if (path == 1) lean_ctor_set(root, 1, lean_box(0));
        }
        lean_object * closure = lean_alloc_closure((void *)worker, 2, 1);
        lean_closure_set(closure, 0, root);
        tasks[i] = lean_task_spawn_core(closure, 0, false);
    }
    /* All worker references exist before the main thread releases its publication reference. */
    lean_dec(shared);
    atomic_store_explicit(&started, true, memory_order_release);
    for (unsigned i = 0; i < WORKERS; ++i) {
        CHECK(lean_task_get(tasks[i]) == lean_box(0));
        lean_dec(tasks[i]);
    }
    CHECK(atomic_load_explicit(&finalized, memory_order_relaxed) == 1);
}

int main(void) {
    lean_initialize_runtime_module();
    lean_init_task_manager_using(WORKERS);
    marker_class = lean_register_external_class(finalize, foreach);
    for (unsigned r = 0; r < ROUNDS; ++r)
        for (unsigned p = 0; p < 4; ++p) shared_case(p);
    lean_finalize_task_manager();
    printf("128 shared root/scanner/unary/borrow cases; eight workers; exactly-once finalization\n");
    return 0;
}
