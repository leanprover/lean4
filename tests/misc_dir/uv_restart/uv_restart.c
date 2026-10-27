/*
Tests of the libuv event loop across `lean_finalize_task_manager`, as an embedder that finalizes and
re-initializes the task manager sees it.

* Each `lean_init_task_manager` after a finalization starts a fresh event loop, so a timer created in
  that cycle fires.
* Between cycles the event loop is torn down: it is not alive, and creating a timer fails.
* A timer, signal or TCP socket created in one cycle and used in a later one fails, since the teardown
  closed its handle. On a closed handle libuv would assert when starting the signal, and `listen` would
  open a new socket for the closed handle and register it with the new loop.

Leaks are reported in the sanitize build. The signal is SIGWINCH, so the test does not run on Windows.
*/
#include <lean/lean.h>

// `leanc` ships no C library headers, but links the C library.
int printf(char const * fmt, ...);
int usleep(unsigned int usec);

void lean_initialize_runtime_module(void);
lean_object * lean_uv_timer_mk(uint64_t timeout, uint8_t repeating);
lean_object * lean_uv_timer_next(lean_object * timer);
lean_object * lean_uv_signal_mk(uint32_t signum, uint8_t repeating);
lean_object * lean_uv_signal_next(lean_object * signal);
lean_object * lean_uv_tcp_new(void);
lean_object * lean_uv_tcp_listen(lean_object * socket, int32_t backlog);
uint8_t lean_uv_event_loop_alive(void);

static int g_failures = 0;

#define CHECK(c) do { \
    if (!(c)) { printf("%s:%d: check failed: %s\n", __FILE__, __LINE__, #c); g_failures++; } \
} while (0)

/* The value of an `IO` result that must succeed, or null. */
static lean_object * take_ok(lean_object * r, char const * what) {
    if (!lean_io_result_is_ok(r)) {
        printf("%s failed\n", what);
        g_failures++;
        lean_dec(r);
        return NULL;
    }
    lean_object * v = lean_io_result_get_value(r);
    lean_inc(v);
    lean_dec(r);
    return v;
}

static void expect_error(lean_object * r, char const * what) {
    if (lean_io_result_is_ok(r)) {
        printf("%s succeeded\n", what);
        g_failures++;
    }
    lean_dec(r);
}

/* Whether a 10 ms timer created now fires within 2 s. */
static int timer_fires(void) {
    lean_object * timer = take_ok(lean_uv_timer_mk(10, 0), "Timer.mk");
    if (timer == NULL)
        return 0;
    int fired = 0;
    lean_object * promise = take_ok(lean_uv_timer_next(timer), "Timer.next");
    if (promise != NULL) {
        lean_object * result = (lean_object *)lean_to_promise(promise)->m_result;
        for (int i = 0; i < 200 && !fired; i++) {
            if (lean_io_get_task_state_core(result) == LEAN_TASK_STATE_FINISHED)
                fired = 1;
            else
                usleep(10000);
        }
        lean_dec(promise);
    }
    lean_dec(timer);
    return fired;
}

int main(void) {
    lean_initialize_runtime_module();

    lean_init_task_manager_using(2);
    CHECK(timer_fires());
    lean_object * timer = take_ok(lean_uv_timer_mk(10, 0), "Timer.mk");
    lean_object * signal = take_ok(lean_uv_signal_mk(28, 1), "Signal.mk");
    lean_object * socket = take_ok(lean_uv_tcp_new(), "TCP.Socket.new");
    lean_finalize_task_manager();

    CHECK(!lean_uv_event_loop_alive());
    expect_error(lean_uv_timer_mk(10, 0), "Timer.mk between cycles");

    lean_init_task_manager_using(2);
    CHECK(timer_fires());
    if (timer != NULL) {
        expect_error(lean_uv_timer_next(timer), "Timer.next on a timer from the previous cycle");
        lean_dec(timer);
    }
    if (signal != NULL) {
        expect_error(lean_uv_signal_next(signal), "Signal.next on a signal from the previous cycle");
        lean_dec(signal);
    }
    if (socket != NULL) {
        expect_error(lean_uv_tcp_listen(socket, 1), "listen on a socket from the previous cycle");
        lean_dec(socket);
    }
    lean_finalize_task_manager();

    lean_init_task_manager_using(2);
    CHECK(timer_fires());
    lean_finalize_task_manager();

    if (g_failures != 0) {
        printf("%d check(s) failed\n", g_failures);
        return 1;
    }
    return 0;
}
