#include <assert.h>
#include <pthread.h>
#include <stdlib.h>

#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

static pthread_t g_caller_thread;
static pthread_t g_observed_thread;
static int g_observed_argc;

static lean_object * inline_main(int argc, char ** argv) {
    (void)argv;
    g_observed_thread = pthread_self();
    g_observed_argc = argc;
    return lean_io_result_mk_ok(lean_box(9));
}

int main(void) {
    assert(setenv("LEAN_MAIN_USE_THREAD", "0", 1) == 0);
    assert(unsetenv("LEAN_STACK_SIZE_KB") == 0);

    lean_initialize_runtime_module();
    lean_initialize_thread();

    char * argv[] = {"lean", "--inline", NULL};
    g_caller_thread = pthread_self();
    lean_object * result = lean_run_main(&inline_main, 2, argv);

    assert(result != NULL);
    assert(lean_io_result_is_ok(result));
    assert(lean_unbox(lean_io_result_get_value(result)) == 9);
    assert(pthread_equal(g_caller_thread, g_observed_thread) != 0);
    assert(g_observed_argc == 2);
    lean_dec_ref(result);

    lean_finalize_thread();
    unsetenv("LEAN_MAIN_USE_THREAD");
    return 0;
}
