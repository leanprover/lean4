/* Task destruction with an active task manager, for tasks with and without
   `LEAN_TASK_PURE_MARKER`. External finalizers check that each value is released exactly once. */
#include <lean/lean.h>

int printf(char const * fmt, ...);
void lean_initialize_runtime_module(void);
lean_obj_res lean_io_promise_new(void);
lean_obj_res lean_io_promise_resolve(lean_obj_arg value, b_lean_obj_arg promise);
lean_obj_res lean_io_promise_result_opt(b_lean_obj_arg promise);

static _Atomic(int) g_failures;
static lean_external_class * g_class;

#define CHECK(c) do { \
    if (!(c)) { printf("%s:%d: check failed: %s\n", __FILE__, __LINE__, #c); \
        atomic_fetch_add(&g_failures, 1); } \
} while (0)

static void finalize(void * data) {
    atomic_fetch_add((_Atomic(int) *)data, 1);
}

static void foreach(void * data, b_lean_obj_arg f) {}

static lean_object * tracked(_Atomic(int) * count) {
    return lean_alloc_external(g_class, count);
}

static lean_object * constant(lean_obj_arg result, lean_obj_arg value) {
    lean_dec(value);
    return result;
}

static void test_pure(void) {
    _Atomic(int) count = 0;
    lean_object * t = lean_task_pure(tracked(&count));
    CHECK(lean_ptr_other(t) == LEAN_TASK_PURE_MARKER);
    lean_dec(t);
    CHECK(count == 1);

    count = 0;
    lean_object * value = tracked(&count);
    lean_inc(value);
    t = lean_task_pure(value);
    lean_dec(t);
    CHECK(count == 0);
    lean_dec(value);
    CHECK(count == 1);
}

static lean_object * release_after(lean_obj_arg t, lean_obj_arg gate, lean_obj_arg unit) {
    lean_task_get(gate);
    lean_dec(gate);
    CHECK(lean_is_external(lean_task_get(t)));
    lean_dec(t);
    return lean_box(0);
}

/* Capturing the task in a spawned closure marks it MT; the worker drops the last reference. */
static void test_mt(void) {
    _Atomic(int) count = 0;
    lean_object * t = lean_task_pure(tracked(&count));
    lean_object * p = lean_io_promise_new();
    lean_inc(t);
    lean_object * f = lean_alloc_closure((void *)release_after, 3, 2);
    lean_closure_set(f, 0, t);
    lean_closure_set(f, 1, lean_io_promise_result_opt(p));
    lean_object * worker = lean_task_spawn_core(f, 0, false);
    CHECK(lean_is_mt(t));
    CHECK(lean_ptr_other(t) == LEAN_TASK_PURE_MARKER);
    lean_dec(t);
    CHECK(count == 0);
    lean_io_promise_resolve(lean_box(0), p);
    lean_task_get(worker);
    lean_dec(worker);
    CHECK(count == 1);
    lean_dec(p);
}

/* Tasks without the marker can be destroyed before they have a value. Dropping a waiting map
   releases its closure at once. */
static void test_unfinished(void) {
    _Atomic(int) count = 0;
    lean_object * p = lean_io_promise_new();
    lean_object * pending = lean_io_promise_result_opt(p);
    CHECK(lean_ptr_other(pending) == 0);
    lean_object * f = lean_alloc_closure((void *)constant, 2, 1);
    lean_closure_set(f, 0, tracked(&count));
    lean_object * t = lean_task_map_core(f, pending, 0, false, false);
    CHECK(lean_ptr_other(t) == 0);
    lean_dec(t);
    CHECK(count == 1);
    lean_dec(p);
}

int main(void) {
    lean_initialize_runtime_module();
    g_class = lean_register_external_class(finalize, foreach);
    lean_init_task_manager_using(4);
    test_pure();
    test_mt();
    test_unfinished();
    lean_finalize_task_manager();
    return g_failures != 0;
}
