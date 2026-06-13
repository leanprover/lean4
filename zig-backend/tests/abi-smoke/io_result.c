#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern uint8_t lean_io_initializing(void);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);

static lean_object * threaded_ok_main(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    return lean_io_result_mk_ok(lean_box(5));
}

static void assert_result_shape(lean_object * result, unsigned expected_tag, uintptr_t expected_payload) {
    assert(result != NULL);
    assert(!lean_is_scalar(result));
    assert(lean_obj_tag(result) == expected_tag);
    assert(lean_ctor_num_objs(result) == 1);
    assert(lean_object_byte_size(result) == sizeof(lean_ctor_object) + sizeof(void *));
    assert(lean_ctor_get(result, 0) == lean_box(expected_payload));
}

static void test_direct_helper_layout_and_size(void) {
    lean_object * ok = lean_io_result_mk_ok(lean_box(0));
    lean_object * err = lean_io_result_mk_error(lean_box(1));
    lean_object * ok_expected = lean_alloc_ctor(0, 1, 0);
    lean_object * err_expected = lean_alloc_ctor(1, 1, 0);

    lean_ctor_set(ok_expected, 0, lean_box(0));
    lean_ctor_set(err_expected, 0, lean_box(1));

    assert_result_shape(ok, 0, 0);
    assert_result_shape(err, 1, 1);
    assert(lean_object_byte_size(ok) == lean_object_byte_size(ok_expected));
    assert(lean_object_byte_size(err) == lean_object_byte_size(err_expected));

    lean_dec_ref(ok);
    lean_dec_ref(err);
    lean_dec_ref(ok_expected);
    lean_dec_ref(err_expected);
}

static void test_initialization_flag(void) {
    assert(lean_io_initializing() != 0);
    lean_io_mark_end_initialization();
    assert(lean_io_initializing() == 0);
}

static void test_run_main_result_release_balances_counters(void) {
    assert(unsetenv("LEAN_MAIN_USE_THREAD") == 0);
    leanrt_test_allocator_reset_counters();

    lean_object * result = lean_run_main(&threaded_ok_main, 0, NULL);
    assert_result_shape(result, 0, 5);
    lean_dec_ref(result);

    assert(leanrt_test_allocator_alloc_count() == leanrt_test_allocator_free_count());
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    test_direct_helper_layout_and_size();
    test_initialization_flag();
    test_run_main_result_release_balances_counters();

    lean_finalize_thread();
    return 0;
}
