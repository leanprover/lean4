#include <assert.h>
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>

#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

static size_t g_observed_stack_size;

static lean_object * stack_probe_main(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    g_observed_stack_size = pthread_get_stacksize_np(pthread_self());
    return lean_io_result_mk_ok(lean_box(0));
}

static void assert_stack_size_near(size_t expected) {
    const size_t page_size = (size_t)getpagesize();
    assert(g_observed_stack_size + page_size >= expected);
    assert(g_observed_stack_size <= expected + page_size);
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    assert(setenv("LEAN_STACK_SIZE_KB", "64", 1) == 0);
    lean_object * small_stack_result = lean_run_main(&stack_probe_main, 0, NULL);
    assert(small_stack_result != NULL);
    assert(lean_io_result_is_ok(small_stack_result));
    assert_stack_size_near(64u * 1024u);
    lean_dec_ref(small_stack_result);

    assert(unsetenv("LEAN_STACK_SIZE_KB") == 0);
    lean_object * default_stack_result = lean_run_main(&stack_probe_main, 0, NULL);
    assert(default_stack_result != NULL);
    assert(lean_io_result_is_ok(default_stack_result));
    assert_stack_size_near(8192u * 1024u);
    lean_dec_ref(default_stack_result);

    lean_finalize_thread();
    return 0;
}
