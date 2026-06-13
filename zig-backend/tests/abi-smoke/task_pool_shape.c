#include <assert.h>
#include <limits.h>
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

extern void leanrt_test_task_manager_reset(void);
extern unsigned leanrt_test_task_manager_default_worker_count(void);
extern _Bool leanrt_test_task_manager_init_from_env(void);
extern void leanrt_test_task_manager_snapshot(leanrt_task_manager_snapshot * out);
extern _Bool leanrt_test_task_manager_spawn_sync_task(void);
extern _Bool leanrt_test_task_manager_spawn_standard_task(unsigned prio);
extern _Bool leanrt_test_task_manager_spawn_dedicated_task(unsigned prio);
extern _Bool leanrt_test_task_manager_contention_smoke(unsigned thread_count);
extern void leanrt_test_task_manager_finalize(void);

static leanrt_task_manager_snapshot snapshot(void) {
    leanrt_task_manager_snapshot out;
    leanrt_test_task_manager_snapshot(&out);
    return out;
}

static void assert_queue_lengths_zero(const leanrt_task_manager_snapshot * snap) {
    for (unsigned i = 0; i < TEST_PRIORITY_QUEUE_COUNT; ++i) {
        assert(snap->queue_lengths[i] == 0);
    }
}

static void test_shape_and_default_workers(void) {
    unsetenv("LEAN_NUM_THREADS");
    leanrt_test_task_manager_reset();
    assert(leanrt_test_task_manager_init_from_env());

    leanrt_task_manager_snapshot snap = snapshot();
    assert(snap.queue_count == TEST_PRIORITY_QUEUE_COUNT);
    assert(snap.lock_count == 1);
    assert(snap.condvar_count == 2);
    assert(snap.worker_count == 0);
    assert(snap.max_std_workers == leanrt_test_task_manager_default_worker_count());
    assert_queue_lengths_zero(&snap);

    leanrt_test_task_manager_finalize();
}

static void test_env_override(void) {
    assert(setenv("LEAN_NUM_THREADS", "4", 1) == 0);
    leanrt_test_task_manager_reset();
    assert(leanrt_test_task_manager_init_from_env());

    leanrt_task_manager_snapshot snap = snapshot();
    assert(snap.max_std_workers == 4);

    leanrt_test_task_manager_finalize();
}

static void test_sync_and_standard_paths(void) {
    assert(setenv("LEAN_NUM_THREADS", "1", 1) == 0);
    leanrt_test_task_manager_reset();
    assert(leanrt_test_task_manager_init_from_env());
    assert(leanrt_test_task_manager_spawn_sync_task());

    leanrt_task_manager_snapshot snap = snapshot();
    assert(snap.worker_count == 0);
    assert(snap.inline_runs == 1);

    assert(leanrt_test_task_manager_spawn_standard_task(0));
    snap = snapshot();
    assert(snap.worker_count == 1);
    assert(snap.standard_runs == 1);

    leanrt_test_task_manager_finalize();
}

static void test_dedicated_path(void) {
    assert(setenv("LEAN_NUM_THREADS", "0", 1) == 0);
    leanrt_test_task_manager_reset();
    assert(leanrt_test_task_manager_init_from_env());
    assert(leanrt_test_task_manager_spawn_dedicated_task(TEST_LEAN_MAX_PRIO + 1));

    leanrt_task_manager_snapshot snap = snapshot();
    assert(snap.max_std_workers == 0);
    assert(snap.worker_count == 0);
    assert(snap.dedicated_started == 1);
    assert(snap.dedicated_finished == 1);
    assert(snap.dedicated_runs == 1);

    leanrt_test_task_manager_finalize();
}

static void test_single_mutex_condvar_contention(void) {
    assert(setenv("LEAN_NUM_THREADS", "1", 1) == 0);
    leanrt_test_task_manager_reset();
    assert(leanrt_test_task_manager_init_from_env());
    assert(leanrt_test_task_manager_contention_smoke(8));
    leanrt_test_task_manager_finalize();
}

int main(void) {
    test_shape_and_default_workers();
    test_env_override();
    test_sync_and_standard_paths();
    test_dedicated_path();
    test_single_mutex_condvar_contention();
    unsetenv("LEAN_NUM_THREADS");
    return 0;
}
