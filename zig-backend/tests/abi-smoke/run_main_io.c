#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

static pthread_t g_caller_thread;
static pthread_t g_worker_thread;

static lean_object * threaded_ok_main(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    g_worker_thread = pthread_self();
    return lean_io_result_mk_ok(lean_box(11));
}

static lean_object * threaded_error_main(int argc, char ** argv) {
    (void)argc;
    (void)argv;
    fputs("panic: synthetic lean_run_main error\n", stderr);
    fflush(stderr);
    return lean_io_result_mk_error(lean_box(13));
}

int main(void) {
    assert(unsetenv("LEAN_MAIN_USE_THREAD") == 0);
    assert(unsetenv("LEAN_STACK_SIZE_KB") == 0);

    lean_initialize_runtime_module();
    lean_initialize_thread();
    g_caller_thread = pthread_self();

    lean_object * ok_result = lean_run_main(&threaded_ok_main, 0, NULL);
    assert(ok_result != NULL);
    assert(lean_io_result_is_ok(ok_result));
    assert(lean_unbox(lean_io_result_get_value(ok_result)) == 11);
    assert(pthread_equal(g_caller_thread, g_worker_thread) == 0);
    lean_dec_ref(ok_result);

    lean_object * error_result = lean_run_main(&threaded_error_main, 0, NULL);
    assert(error_result != NULL);
    assert(lean_io_result_is_error(error_result));
    assert(lean_unbox(lean_io_result_get_error(error_result)) == 13);
    lean_dec_ref(error_result);

    lean_finalize_thread();
    return 0;
}
