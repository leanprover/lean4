#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>

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

typedef struct {
    unsigned joined_standard_workers;
    unsigned dedicated_started;
    unsigned dedicated_finished;
    unsigned pending_dedicated_workers;
    _Bool saw_shutdown;
    _Bool manager_active_after_finalize;
} leanrt_runtime_finalize_summary;

extern _Bool leanrt_test_runtime_task_manager_active(void);
extern void leanrt_test_runtime_task_manager_snapshot(leanrt_task_manager_snapshot * out);
extern void leanrt_test_runtime_task_manager_last_finalize_summary(leanrt_runtime_finalize_summary * out);
extern lean_object * leanrt_test_runtime_spawn_sleep_task(unsigned prio, unsigned sleep_ms);

static long elapsed_ms(struct timespec start, struct timespec stop) {
    const long sec = stop.tv_sec - start.tv_sec;
    const long nsec = stop.tv_nsec - start.tv_nsec;
    return sec * 1000L + nsec / 1000000L;
}

static leanrt_task_manager_snapshot snapshot(void) {
    leanrt_task_manager_snapshot out;
    leanrt_test_runtime_task_manager_snapshot(&out);
    return out;
}

int main(void) {
    struct timespec start;
    struct timespec stop;

    lean_init_task_manager_using(1);
    assert(leanrt_test_runtime_task_manager_active());

    lean_object * standard = leanrt_test_runtime_spawn_sleep_task(0, 50);
    lean_object * dedicated = leanrt_test_runtime_spawn_sleep_task(TEST_LEAN_MAX_PRIO + 1u, 75);
    assert(standard != NULL);
    assert(dedicated != NULL);

    const leanrt_task_manager_snapshot before = snapshot();
    assert(before.worker_count >= 1);
    assert(before.dedicated_started >= 1);

    assert(clock_gettime(CLOCK_MONOTONIC, &start) == 0);
    lean_finalize_task_manager();
    assert(clock_gettime(CLOCK_MONOTONIC, &stop) == 0);

    leanrt_runtime_finalize_summary summary;
    leanrt_test_runtime_task_manager_last_finalize_summary(&summary);

    assert(!leanrt_test_runtime_task_manager_active());
    assert(elapsed_ms(start, stop) < 1000L);
    assert(summary.joined_standard_workers >= 1);
    assert(summary.dedicated_started >= 1);
    assert(summary.dedicated_finished == summary.dedicated_started);
    assert(summary.pending_dedicated_workers == 0);
    assert(summary.saw_shutdown);
    assert(!summary.manager_active_after_finalize);

    lean_dec(standard);
    lean_dec(dedicated);
    return 0;
}
