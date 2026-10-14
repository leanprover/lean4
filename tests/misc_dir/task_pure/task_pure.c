/* Task lifetime tests with an active task manager. Promises order ownership transfers;
   external finalizers check that heap values are released exactly once. */
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

static lean_object * identity(lean_obj_arg value) { return value; }

static lean_object * pure(lean_obj_arg value) { return lean_task_pure(value); }

static lean_object * constant(lean_obj_arg result, lean_obj_arg value) {
    lean_dec(value);
    return result;
}

static lean_object * closure1(void * fn) { return lean_alloc_closure(fn, 1, 0); }

static lean_object * capture_task(lean_obj_arg task) {
    lean_object * f = lean_alloc_closure((void *)constant, 2, 1);
    lean_closure_set(f, 0, task);
    return f;
}

static void test_values(void) {
    lean_object * t = lean_task_pure(lean_box(42));
    CHECK(lean_unbox(lean_task_get(t)) == 42);
    lean_dec(t);

    _Atomic(int) count = 0;
    lean_object * value = tracked(&count);
    lean_inc(value);
    t = lean_task_pure(value);
    CHECK(lean_task_get(t) == value);
    lean_dec(t);
    CHECK(count == 0);
    lean_dec(value);
    CHECK(count == 1);

    count = 0;
    t = lean_task_pure(tracked(&count));
    for (unsigned i = 0; i < 32; i++) t = lean_task_pure(t);
    /* Exercise the deletion worklist's header packing as well as direct decrements. */
    lean_object * parent = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(parent, 0, t);
    lean_dec(parent);
    CHECK(count == 1);
}

static void test_sync(void) {
    _Atomic(int) count = 0;
    lean_object * t = lean_task_map_core(closure1((void *)identity),
        lean_task_pure(tracked(&count)), 0, true, false);
    CHECK(count == 0);
    lean_dec(t);
    CHECK(count == 1);

    count = 0;
    t = lean_task_bind_core(lean_task_pure(tracked(&count)),
        closure1((void *)pure), 0, true, false);
    CHECK(count == 0);
    lean_dec(t);
    CHECK(count == 1);

    /* A synchronous bind can return an unfinished, promise-backed task. */
    lean_object * p = lean_io_promise_new();
    lean_object * pending = lean_io_promise_result_opt(p);
    count = 0;
    t = lean_task_bind_core(lean_task_pure(tracked(&count)), capture_task(pending),
        0, true, false);
    CHECK(t == pending);
    CHECK(lean_to_task(t)->m_value == NULL);
    CHECK(count == 1);
    lean_io_promise_resolve(tracked(&count), p);
    CHECK(!lean_is_scalar(lean_task_get(t)));
    lean_dec(p);
    CHECK(count == 1);
    lean_dec(t);
    CHECK(count == 2);

    /* A waiting bind must also survive its callback's unfinished result. */
    p = lean_io_promise_new();
    lean_object * q = lean_io_promise_new();
    t = lean_task_bind_core(lean_io_promise_result_opt(p),
        capture_task(lean_io_promise_result_opt(q)), 0, true, false);
    lean_io_promise_resolve(lean_box(0), p);
    CHECK(lean_to_task(t)->m_value == NULL);
    lean_io_promise_resolve(tracked(&count), q);
    CHECK(!lean_is_scalar(lean_task_get(t)));
    lean_dec(p);
    lean_dec(q);
    CHECK(count == 2);
    lean_dec(t);
    CHECK(count == 3);
}

/* Each worker owns one reference to the pure task and waits until the main thread
   has released its reference. The final release therefore occurs on a worker. */
static lean_object * release_shared(lean_obj_arg t, lean_obj_arg gate, lean_obj_arg unit) {
    lean_task_get(gate);
    lean_dec(gate);
    CHECK(lean_is_external(lean_task_get(t)));
    lean_dec(t);
    return lean_box(0);
}

static void test_shared(void) {
    _Atomic(int) count = 0;
    lean_object * t = lean_task_pure(tracked(&count));
    lean_object * p = lean_io_promise_new();
    lean_object * workers[4];
    for (unsigned i = 0; i < 4; i++) {
        lean_inc(t);
        lean_object * f = lean_alloc_closure((void *)release_shared, 3, 2);
        lean_closure_set(f, 0, t);
        lean_closure_set(f, 1, lean_io_promise_result_opt(p));
        workers[i] = lean_task_spawn_core(f, 0, false);
    }
    CHECK(lean_is_mt(t));
    lean_dec(t);
    CHECK(count == 0);
    lean_io_promise_resolve(lean_box(0), p);
    for (unsigned i = 0; i < 4; i++) {
        lean_task_get(workers[i]);
        lean_dec(workers[i]);
    }
    CHECK(count == 1);
    lean_dec(p);
}

static lean_object * run_gated(lean_obj_arg value, lean_obj_arg started,
        lean_obj_arg gate, lean_obj_arg unit) {
    lean_io_promise_resolve(lean_box(0), started);
    lean_dec(started);
    lean_task_get(gate);
    lean_dec(gate);
    return value;
}

static void test_scheduled(_Atomic(int) * running_count) {
    /* A finished scheduled task still needs scheduler synchronization at destruction. */
    _Atomic(int) count = 0;
    lean_object * t = lean_task_map_core(closure1((void *)identity),
        lean_task_pure(tracked(&count)), 0, false, false);
    lean_task_get(t);
    lean_dec(t);
    CHECK(count == 1);

    /* Drop the last owned reference while a scheduled task is still running. */
    lean_object * started = lean_io_promise_new();
    lean_object * ready = lean_io_promise_result_opt(started);
    lean_object * gate = lean_io_promise_new();
    lean_object * f = lean_alloc_closure((void *)run_gated, 4, 3);
    lean_closure_set(f, 0, tracked(running_count));
    lean_closure_set(f, 1, started);
    lean_closure_set(f, 2, lean_io_promise_result_opt(gate));
    t = lean_task_spawn_core(f, 0, false);
    lean_task_get(ready);
    lean_dec(ready);
    lean_dec(t);
    CHECK(*running_count == 0);
    lean_io_promise_resolve(lean_box(0), gate);
    lean_dec(gate);
}

static void test_promises(void) {
    _Atomic(int) count = 0;
    lean_object * p = lean_io_promise_new();
    lean_object * t = lean_io_promise_result_opt(p);
    /* A waiting map is released before its dependency completes. */
    lean_object * f = lean_alloc_closure((void *)constant, 2, 1);
    lean_closure_set(f, 0, tracked(&count));
    lean_dec(lean_task_map_core(f, lean_io_promise_result_opt(p), 0, true, false));
    CHECK(count == 1);
    lean_io_promise_resolve(tracked(&count), p);
    lean_io_promise_resolve(tracked(&count), p);
    CHECK(count == 2); /* The second value is discarded. */
    lean_dec(p);
    CHECK(count == 2);
    lean_dec(t);
    CHECK(count == 3);

    p = lean_io_promise_new();
    t = lean_io_promise_result_opt(p);
    lean_dec(p);
    CHECK(lean_task_get(t) == lean_box(0)); /* An abandoned promise yields none. */
    lean_dec(t);
}

int main(void) {
    lean_initialize_runtime_module();
    g_class = lean_register_external_class(finalize, foreach);
    test_values();
    lean_init_task_manager_using(4);
    test_values();
    test_sync();
    test_shared();
    test_promises();
    _Atomic(int) running_count = 0;
    test_scheduled(&running_count);
    lean_finalize_task_manager(); /* Join workers before checking deferred destruction. */
    CHECK(running_count == 1);
    test_values();
    return g_failures != 0;
}
