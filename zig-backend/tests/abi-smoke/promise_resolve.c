#include <assert.h>
#include <sched.h>
#include <stdatomic.h>
#include <time.h>

#include <lean/lean.h>

extern _Bool leanrt_test_runtime_task_manager_init(unsigned num_workers);
extern void leanrt_test_runtime_task_manager_finalize(void);
extern _Bool leanrt_test_runtime_task_wait(lean_object * task);

extern lean_object * lean_io_promise_new(void);
extern lean_object * lean_io_promise_resolve(lean_object * value, lean_object * promise);
extern lean_object * lean_io_promise_result_opt(lean_object * promise);

static atomic_bool g_bind_ran = false;

static lean_object * unwrap_some_to_task(lean_object * option) {
    assert(!lean_is_scalar(option));
    assert(lean_obj_tag(option) == 1);
    lean_object * value = lean_ctor_get(option, 0);
    lean_inc(value);
    atomic_store_explicit(&g_bind_ran, true, memory_order_release);
    return lean_task_pure(value);
}

static long elapsed_millis(const struct timespec * start, const struct timespec * finish) {
    long sec = finish->tv_sec - start->tv_sec;
    long nsec = finish->tv_nsec - start->tv_nsec;
    return sec * 1000 + nsec / 1000000;
}

int main(void) {
    struct timespec start;
    struct timespec finish;

    assert(leanrt_test_runtime_task_manager_init(1));
    atomic_store_explicit(&g_bind_ran, false, memory_order_release);

    lean_object * promise_obj = lean_io_promise_new();
    lean_object * result_task = lean_io_promise_result_opt(promise_obj);
    lean_inc(result_task);

    lean_object * bind_closure = lean_alloc_closure((void *)unwrap_some_to_task, 1, 0);
    lean_object * bound_task = lean_task_bind_core(result_task, bind_closure, 0, 0, 0);

    clock_gettime(CLOCK_MONOTONIC, &start);
    assert(lean_io_promise_resolve(lean_box(17), promise_obj) == lean_box(0));
    assert(leanrt_test_runtime_task_wait(bound_task));
    clock_gettime(CLOCK_MONOTONIC, &finish);

    assert(atomic_load_explicit(&g_bind_ran, memory_order_acquire));
    assert(elapsed_millis(&start, &finish) < 100);
    assert(lean_unbox(lean_task_get(bound_task)) == 17);
    assert(lean_unbox(lean_ctor_get(lean_task_get(result_task), 0)) == 17);

    lean_dec(result_task);
    lean_dec(promise_obj);
    lean_dec(bound_task);
    leanrt_test_runtime_task_manager_finalize();
    return 0;
}
