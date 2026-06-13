#include <assert.h>
#include <sched.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern _Bool leanrt_test_runtime_task_manager_active(void);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);

static atomic_bool g_release_producer = false;
static atomic_uint g_bind_runs = 0;

static void spin_until_true(atomic_bool * flag) {
    while (!atomic_load_explicit(flag, memory_order_acquire)) {
        sched_yield();
    }
}

static lean_object * blocked_producer(lean_object * unit) {
    (void)unit;
    spin_until_true(&g_release_producer);
    return lean_box(5);
}

static lean_object * bind_to_finished_task(lean_object * value) {
    assert(lean_unbox(value) == 5);
    atomic_fetch_add_explicit(&g_bind_runs, 1, memory_order_acq_rel);
    return lean_task_pure(lean_box(42));
}

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));
    assert(leanrt_test_runtime_task_manager_active());

    atomic_store_explicit(&g_release_producer, false, memory_order_release);
    atomic_store_explicit(&g_bind_runs, 0, memory_order_release);

    lean_object * producer_closure = lean_alloc_closure((void *)blocked_producer, 1, 0);
    lean_object * producer_task = lean_task_spawn_core(producer_closure, 0, 0);
    lean_inc(producer_task);

    lean_object * bind_closure = lean_alloc_closure((void *)bind_to_finished_task, 1, 0);
    lean_object * bound_task = lean_task_bind_core(producer_task, bind_closure, 0, 0, 0);

    lean_task_object * producer = lean_to_task(producer_task);
    lean_task_object * bound = lean_to_task(bound_task);
    assert(producer->m_imp != NULL);
    assert(bound->m_imp != NULL);
    assert(producer->m_imp->m_head_dep == bound);
    assert(bound->m_imp->m_next_dep == NULL);

    atomic_store_explicit(&g_release_producer, true, memory_order_release);
    assert(leanrt_test_runtime_task_wait(bound_task));
    assert(atomic_load_explicit(&g_bind_runs, memory_order_acquire) == 1);
    assert(lean_unbox(atomic_load_explicit(&bound->m_value, memory_order_acquire)) == 42);

    lean_dec(producer_task);
    lean_dec(bound_task);
    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
