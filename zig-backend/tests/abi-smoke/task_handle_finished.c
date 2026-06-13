#include <assert.h>
#include <sched.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);
extern _Bool leanrt_test_runtime_task_mark_deleted(lean_object * task);
extern void leanrt_test_runtime_task_manager_snapshot(void * out);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);
extern void leanrt_test_task_object_counter_reset(void);
extern size_t leanrt_test_task_object_alloc_count(void);
extern size_t leanrt_test_task_object_free_count(void);

#define LEANRT_PRIORITY_QUEUE_COUNT 9

typedef struct {
    unsigned queue_count;
    unsigned lock_count;
    unsigned condvar_count;
    unsigned worker_count;
    unsigned max_std_workers;
    unsigned idle_workers;
    unsigned dedicated_started;
    unsigned dedicated_finished;
    unsigned inline_runs;
    unsigned standard_runs;
    unsigned dedicated_runs;
    unsigned max_prio_seen;
    unsigned queue_lengths[LEANRT_PRIORITY_QUEUE_COUNT];
} leanrt_task_manager_snapshot;

static atomic_bool g_release_producer = false;
static atomic_uint g_deleted_continuation_runs = 0;

static void spin_until_true(atomic_bool * flag) {
    while (!atomic_load_explicit(flag, memory_order_acquire)) {
        sched_yield();
    }
}

static lean_object * blocked_producer(lean_object * unit) {
    (void)unit;
    spin_until_true(&g_release_producer);
    return lean_box(9);
}

static lean_object * deleted_continuation(lean_object * value) {
    assert(lean_unbox(value) == 9);
    atomic_fetch_add_explicit(&g_deleted_continuation_runs, 1, memory_order_acq_rel);
    return lean_task_pure(lean_box(11));
}

static void assert_queues_empty(const leanrt_task_manager_snapshot * snapshot) {
    for (unsigned i = 0; i < LEANRT_PRIORITY_QUEUE_COUNT; ++i) {
        assert(snapshot->queue_lengths[i] == 0);
    }
}

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));
    atomic_store_explicit(&g_release_producer, false, memory_order_release);
    atomic_store_explicit(&g_deleted_continuation_runs, 0, memory_order_release);
    leanrt_test_allocator_reset_counters();
    leanrt_test_task_object_counter_reset();

    lean_object * producer_closure = lean_alloc_closure((void *)blocked_producer, 1, 0);
    lean_object * producer_task = lean_task_spawn_core(producer_closure, 0, 0);

    lean_inc(producer_task);
    lean_object * continuation_closure = lean_alloc_closure((void *)deleted_continuation, 1, 0);
    lean_object * deleted_task = lean_task_bind_core(producer_task, continuation_closure, 0, 0, 0);

    lean_task_object * producer = lean_to_task(producer_task);
    assert(producer->m_imp != NULL);
    assert(producer->m_imp->m_head_dep == lean_to_task(deleted_task));
    assert(leanrt_test_runtime_task_mark_deleted(deleted_task));

    atomic_store_explicit(&g_release_producer, true, memory_order_release);
    assert(leanrt_test_runtime_task_wait(producer_task));

    leanrt_task_manager_snapshot snapshot;
    leanrt_test_runtime_task_manager_snapshot(&snapshot);
    assert(snapshot.standard_runs == 1);
    assert(snapshot.inline_runs == 0);
    assert(snapshot.dedicated_runs == 0);
    assert_queues_empty(&snapshot);
    assert(atomic_load_explicit(&g_deleted_continuation_runs, memory_order_acquire) == 0);

    assert(leanrt_test_task_object_alloc_count() == 2);
    assert(leanrt_test_task_object_free_count() == 1);

    lean_dec(producer_task);
    assert(leanrt_test_task_object_alloc_count() == leanrt_test_task_object_free_count());
    assert(leanrt_test_allocator_alloc_count() == leanrt_test_allocator_free_count());

    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
