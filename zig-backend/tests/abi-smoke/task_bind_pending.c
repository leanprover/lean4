#include <assert.h>
#include <sched.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);
/* Exercises the `task_bind_fn1` nullptr sentinel path. */

static atomic_bool g_release_outer = false;
static atomic_bool g_release_inner = false;
static atomic_uint g_inner_started = 0;
static atomic_uint g_continuation_runs = 0;

static void spin_until_true(atomic_bool * flag) {
    while (!atomic_load_explicit(flag, memory_order_acquire)) {
        sched_yield();
    }
}

static void spin_until_uint(atomic_uint * value, unsigned expected) {
    while (atomic_load_explicit(value, memory_order_acquire) < expected) {
        sched_yield();
    }
}

static lean_object * blocked_outer(lean_object * unit) {
    (void)unit;
    spin_until_true(&g_release_outer);
    return lean_box(7);
}

static lean_object * blocked_inner(lean_object * unit) {
    (void)unit;
    atomic_fetch_add_explicit(&g_inner_started, 1, memory_order_acq_rel);
    spin_until_true(&g_release_inner);
    return lean_box(13);
}

static lean_object * spawn_pending_inner(lean_object * value) {
    assert(lean_unbox(value) == 7);
    atomic_fetch_add_explicit(&g_continuation_runs, 1, memory_order_acq_rel);
    lean_object * inner_closure = lean_alloc_closure((void *)blocked_inner, 1, 0);
    return lean_task_spawn_core(inner_closure, 0, 0);
}

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));

    atomic_store_explicit(&g_release_outer, false, memory_order_release);
    atomic_store_explicit(&g_release_inner, false, memory_order_release);
    atomic_store_explicit(&g_inner_started, 0, memory_order_release);
    atomic_store_explicit(&g_continuation_runs, 0, memory_order_release);

    lean_object * outer_closure = lean_alloc_closure((void *)blocked_outer, 1, 0);
    lean_object * outer_task = lean_task_spawn_core(outer_closure, 0, 0);
    lean_inc(outer_task);

    lean_object * bind_closure = lean_alloc_closure((void *)spawn_pending_inner, 1, 0);
    lean_object * bound_task = lean_task_bind_core(outer_task, bind_closure, 0, 0, 0);
    lean_task_object * bound = lean_to_task(bound_task);

    atomic_store_explicit(&g_release_outer, true, memory_order_release);
    spin_until_uint(&g_inner_started, 1);

    assert(atomic_load_explicit(&g_continuation_runs, memory_order_acquire) == 1);
    assert(atomic_load_explicit(&bound->m_value, memory_order_acquire) == NULL);
    assert(bound->m_imp != NULL);
    assert(bound->m_imp->m_closure != NULL);

    atomic_store_explicit(&g_release_inner, true, memory_order_release);
    assert(leanrt_test_runtime_task_wait(bound_task));
    assert(lean_unbox(atomic_load_explicit(&bound->m_value, memory_order_acquire)) == 13);

    lean_dec(outer_task);
    lean_dec(bound_task);
    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
