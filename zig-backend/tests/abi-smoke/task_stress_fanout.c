#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#include <lean/lean.h>

#define FANOUT_COUNT 1000u

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);
extern void leanrt_test_task_object_counter_reset(void);
extern size_t leanrt_test_task_object_alloc_count(void);
extern size_t leanrt_test_task_object_free_count(void);

static uint64_t wall_clock_nanos(void) {
    struct timeval tv;
    assert(gettimeofday(&tv, NULL) == 0);
    return ((uint64_t)tv.tv_sec * UINT64_C(1000000000)) + ((uint64_t)tv.tv_usec * UINT64_C(1000));
}

static lean_object * fanout_task(lean_object * payload) {
    return payload;
}

int main(void) {
    lean_object * tasks[FANOUT_COUNT];
    uint64_t sum = 0;
    uint64_t started;
    uint64_t elapsed;

    lean_initialize_runtime_module();
    lean_initialize_thread();
    lean_init_task_manager_using(4);

    leanrt_test_allocator_reset_counters();
    leanrt_test_task_object_counter_reset();
    started = wall_clock_nanos();

    for (unsigned i = 0; i < FANOUT_COUNT; ++i) {
        lean_object * closure = lean_alloc_closure((void *)fanout_task, 2, 1);
        lean_closure_set(closure, 0, lean_box(i));
        tasks[i] = lean_task_spawn_core(closure, i % 3u, false);
    }

    for (unsigned i = 0; i < FANOUT_COUNT; ++i) {
        lean_object * value = lean_task_get(tasks[i]);
        sum += (uint64_t)lean_unbox(value);
        lean_dec(tasks[i]);
    }

    elapsed = wall_clock_nanos() - started;
    lean_finalize_task_manager();
    lean_finalize_thread();

    assert(sum == ((uint64_t)(FANOUT_COUNT - 1u) * (uint64_t)FANOUT_COUNT) / 2u);
    assert(elapsed < UINT64_C(30000000000));
    assert(leanrt_test_allocator_alloc_count() == leanrt_test_allocator_free_count());
    assert(leanrt_test_task_object_alloc_count() == leanrt_test_task_object_free_count());

    printf(
        "task-stress-fanout: count=%u elapsed_ms=%llu alloc=%zu free=%zu\n",
        FANOUT_COUNT,
        (unsigned long long)(elapsed / UINT64_C(1000000)),
        leanrt_test_allocator_alloc_count(),
        leanrt_test_allocator_free_count());
    return 0;
}
