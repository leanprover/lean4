#include <assert.h>
#include <stdlib.h>

#include <lean/lean.h>

#define TEST_LEAN_MAX_PRIO 8u
#define TEST_PRIORITY_QUEUE_COUNT (TEST_LEAN_MAX_PRIO + 1u)

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
    unsigned queue_lengths[TEST_PRIORITY_QUEUE_COUNT];
} leanrt_task_manager_snapshot;

extern _Bool leanrt_test_runtime_task_manager_active(void);
extern void leanrt_test_runtime_task_manager_snapshot(leanrt_task_manager_snapshot * out);

static leanrt_task_manager_snapshot snapshot(void) {
    leanrt_task_manager_snapshot out;
    leanrt_test_runtime_task_manager_snapshot(&out);
    return out;
}

static void test_explicit_worker_override(void) {
    lean_init_task_manager_using(3);
    assert(leanrt_test_runtime_task_manager_active());

    leanrt_task_manager_snapshot snap = snapshot();
    assert(snap.queue_count == TEST_PRIORITY_QUEUE_COUNT);
    assert(snap.max_std_workers == 3);

    lean_finalize_task_manager();
    assert(!leanrt_test_runtime_task_manager_active());
}

static void test_env_wrapper(void) {
    assert(setenv("LEAN_NUM_THREADS", "2", 1) == 0);

    lean_init_task_manager();
    assert(leanrt_test_runtime_task_manager_active());
    assert(snapshot().max_std_workers == 2);

    lean_finalize_task_manager();
    assert(!leanrt_test_runtime_task_manager_active());
}

static void test_zero_worker_init_and_reinit_cycle(void) {
    lean_init_task_manager_using(0);
    assert(!leanrt_test_runtime_task_manager_active());
    lean_finalize_task_manager();

    lean_init_task_manager_using(1);
    assert(leanrt_test_runtime_task_manager_active());
    assert(snapshot().max_std_workers == 1);
    lean_finalize_task_manager();
}

int main(void) {
    unsetenv("LEAN_NUM_THREADS");
    test_explicit_worker_override();
    test_env_wrapper();
    unsetenv("LEAN_NUM_THREADS");
    test_zero_worker_init_and_reinit_cycle();
    return 0;
}
