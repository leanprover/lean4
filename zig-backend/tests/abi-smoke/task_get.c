#include <assert.h>
#include <time.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);

static lean_object * delayed_producer(lean_object * unit) {
    (void)unit;
    const struct timespec delay = {.tv_sec = 0, .tv_nsec = 50 * 1000 * 1000};
    nanosleep(&delay, NULL);
    return lean_box(42);
}

static long elapsed_ms(const struct timespec *start, const struct timespec *end) {
    return (end->tv_sec - start->tv_sec) * 1000L + (end->tv_nsec - start->tv_nsec) / 1000L / 1000L;
}

int main(void) {
    assert(leanrt_test_runtime_task_manager_init(1));

    lean_object *closure = lean_alloc_closure((void *)delayed_producer, 1, 0);
    lean_object *task = lean_task_spawn_core(closure, 0, 0);

    struct timespec start;
    struct timespec end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    lean_object *value = lean_task_get(task);
    clock_gettime(CLOCK_MONOTONIC, &end);

    assert(value != NULL);
    assert(lean_unbox(value) == 42);
    assert(elapsed_ms(&start, &end) >= 20);

    lean_dec(task);
    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
