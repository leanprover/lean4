#include <assert.h>
#include <stdlib.h>
#include <stdatomic.h>

#include <lean/lean.h>

extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern lean_object * lean_io_promise_new(void);
extern lean_object * lean_io_promise_resolve(lean_object * value, lean_object * promise);
extern lean_object * lean_io_promise_result_opt(lean_object * promise);

static lean_object * mk_thunk_object(lean_object * closure) {
    lean_thunk_object * thunk = (lean_thunk_object *)lean_alloc_object(sizeof(lean_thunk_object));
    lean_set_st_header((lean_object *)thunk, LeanThunk, 0);
    atomic_store_explicit(&thunk->m_value, NULL, memory_order_relaxed);
    atomic_store_explicit(&thunk->m_closure, closure, memory_order_relaxed);
    return (lean_object *)thunk;
}

static lean_object * spawn_body(lean_object * unit) {
    (void)unit;
    return lean_box(5);
}

static lean_object * bind_body(lean_object * value) {
    assert(lean_unbox(value) == 5);
    return lean_task_pure(lean_box(12));
}

static lean_object * map_body(lean_object * value) {
    return lean_box(lean_unbox(value) + 7);
}

static lean_object * thunk_body(lean_object * unit) {
    (void)unit;
    return lean_box(21);
}

static lean_object * run_main_body(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    return lean_io_result_mk_ok(lean_box(34));
}

static void test_task_symbols(void) {
    lean_object * pure_task = lean_task_pure(lean_box(1));
    assert(lean_unbox(lean_task_get(pure_task)) == 1);
    lean_dec(pure_task);

    lean_object * spawn_task = lean_task_spawn_core(lean_alloc_closure((void *)spawn_body, 1, 0), 0, false);
    lean_inc(spawn_task);
    lean_object * bound_task = lean_task_bind_core(
        spawn_task,
        lean_alloc_closure((void *)bind_body, 1, 0),
        0,
        false,
        false);
    assert(lean_unbox(lean_task_get(bound_task)) == 12);

    lean_object * mapped_task = lean_task_map_core(
        lean_alloc_closure((void *)map_body, 1, 0),
        lean_task_pure(lean_box(3)),
        0,
        true,
        false);
    assert(lean_unbox(lean_task_get(mapped_task)) == 10);

    lean_dec(spawn_task);
    lean_dec(bound_task);
    lean_dec(mapped_task);
}

static void test_promise_symbols(void) {
    lean_object * promise = lean_io_promise_new();
    lean_object * result_task = lean_io_promise_result_opt(promise);
    lean_object * option;

    assert(lean_unbox(lean_io_promise_resolve(lean_box(8), promise)) == 0);
    option = lean_task_get(result_task);
    assert(lean_obj_tag(option) == 1);
    assert(lean_unbox(lean_ctor_get(option, 0)) == 8);

    lean_dec(result_task);
    lean_dec(promise);
}

static void test_run_main_and_thunk(void) {
    lean_object * thunk = mk_thunk_object(lean_alloc_closure((void *)thunk_body, 1, 0));
    lean_object * io_result = lean_run_main(&run_main_body, 0, NULL);

    assert(lean_unbox(lean_thunk_get_own(thunk)) == 21);
    assert(lean_io_result_is_ok(io_result));
    assert(lean_unbox(lean_io_result_get_value(io_result)) == 34);
    lean_dec_ref(io_result);
}

int main(void) {
    assert(unsetenv("LEAN_NUM_THREADS") == 0);

    lean_initialize_thread();

    lean_init_task_manager_using(1);
    test_task_symbols();
    test_promise_symbols();
    lean_finalize_task_manager();

    assert(setenv("LEAN_NUM_THREADS", "1", 1) == 0);
    lean_init_task_manager();
    test_run_main_and_thunk();
    lean_finalize_task_manager();

    lean_finalize_thread();
    return 0;
}
