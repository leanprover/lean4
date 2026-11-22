/*
Tests of the libuv event loop across `lean_finalize_task_manager`, as an embedder that finalizes and
re-initializes the task manager sees it.

* Each `lean_init_task_manager` after a finalization starts a fresh event loop, so a timer created in
  that cycle fires.
* Between cycles the event loop is torn down: it is not alive, and creating a timer fails.
* A timer, signal, TCP or UDP socket created in one cycle and used in a later one fails, since the
  teardown closed its handle. On a closed handle libuv would assert when starting the signal, and
  `listen` would open a new socket for the closed handle and register it with the new loop. Sending
  no data, which needs no libuv call, fails too.
* A pending promise that only the event loop references stays pending through the teardown and is
  released when the task manager restarts, which resolves its result with `none` and discards its
  continuations. So a task of the new cycle that waits on it does not keep the next finalization
  waiting. This also holds when the restart waits for a finalization in progress on another thread.
* Concurrent restarts start one event loop.
* Finalizing does not wait for threads the task manager does not own to stop calling into libuv: the
  loop thread gives way to such threads, so while several of them keep taking the loop lock it would
  never see that the loop stopped.
* With the argument `exit_during_teardown`, `exit` while another thread tears the event loop down does
  not free what the teardown still uses. The sanitize build reports a use of freed memory.
* With `wait_exited_child_from_loop`, a continuation on the loop thread can wait for a task that waits for
  a child that has already exited.
* With `wait_across_teardown`, a thread blocked in `Child.wait` when the teardown closes the child's
  handle fails with `ECANCELED` instead of waiting forever, and so does a later `tryWait`.
* With `zombies`, children that are still running at a teardown are reaped once they have exited.
* With `failed_restart`, an init after a restart that could not start the loop starts it.
* With `signal_during_teardown`, a signal that the program handles does not kill it while the teardown
  runs.
* With `finalize_on_loop_thread`, finalizing from a finalizer that the loop thread runs fails with an
  internal panic instead of joining that thread.

Leaks are reported in the sanitize build. The signal is SIGWINCH and the threads are POSIX threads, so
the test does not run on Windows.
*/
#include <lean/lean.h>

// `leanc` ships no C library headers, but links the C library.
int printf(char const * fmt, ...);
int usleep(unsigned int usec);
int strcmp(char const * a, char const * b);
void exit(int status);
unsigned int alarm(unsigned int seconds);
// `FILE *` is a pointer.
int fflush(void * stream);
// `pthread_t` is a pointer-sized integer or pointer on the platforms this test runs on.
typedef unsigned long long thread_handle;
int pthread_create(thread_handle * thread, void const * attr, void * (*start)(void *), void * arg);
int pthread_join(thread_handle thread, void ** result);
int pthread_detach(thread_handle thread);

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_object * lean_io_promise_result_opt(lean_object * promise);
lean_object * lean_uv_timer_mk(uint64_t timeout, uint8_t repeating);
lean_object * lean_uv_timer_next(lean_object * timer);
lean_object * lean_uv_signal_mk(uint32_t signum, uint8_t repeating);
lean_object * lean_uv_signal_next(lean_object * signal);
lean_object * lean_uv_tcp_new(void);
lean_object * lean_uv_tcp_listen(lean_object * socket, int32_t backlog);
lean_object * lean_uv_tcp_send(lean_object * socket, lean_object * data);
lean_object * lean_uv_udp_new(void);
lean_object * lean_uv_udp_send(lean_object * socket, lean_object * data, lean_object * addr);
uint8_t lean_uv_event_loop_alive(void);
lean_object * lean_uv_random(uint64_t size);
lean_object * lean_io_promise_resolve(lean_object * value, lean_object * promise);
lean_object * lean_io_process_spawn(lean_object * args);
lean_object * lean_io_process_child_wait(lean_object * cfg, lean_object * child);
lean_object * lean_io_process_child_try_wait(lean_object * cfg, lean_object * child);
int waitpid(int pid, int * status, int options);
int getpid(void);
int kill(int pid, int sig);
int dup(int fd);
int close(int fd);
struct rlimit_ { unsigned long long cur, max; };
int getrlimit(int resource, struct rlimit_ * limit);
int setrlimit(int resource, struct rlimit_ const * limit);
#ifdef __APPLE__
#define SIGUSR1_ 30
#define RLIMIT_NOFILE_ 8
#else
#define SIGUSR1_ 10
#define RLIMIT_NOFILE_ 7
#endif

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

/* The result of the promise of a timer that does not fire before the next finalization, or null. The
   event loop holds the only reference to the promise. */
static lean_object * pending_timer_result(void) {
    lean_object * timer = take_ok(lean_uv_timer_mk(3600000, 0), "Timer.mk");
    if (timer == NULL)
        return NULL;
    lean_object * promise = take_ok(lean_uv_timer_next(timer), "Timer.next");
    lean_dec(timer);
    if (promise == NULL)
        return NULL;
    lean_object * result = lean_io_promise_result_opt(promise);
    lean_dec(promise);
    return result;
}

static int g_continuation_runs = 0;

static lean_object * count_run(lean_object * value) {
    g_continuation_runs++;
    lean_dec(value);
    return lean_box(0);
}

/* Expects the task manager to be running, and leaves it running. */
static void check_pending_promise_released_at_restart(void) {
    lean_object * result = pending_timer_result();
    if (result == NULL)
        return;
    lean_inc(result);
    lean_object * continuation = lean_task_map_core(lean_alloc_closure((void *)count_run, 1, 0), result, 0, 1, 0);

    lean_finalize_task_manager();
    CHECK(lean_io_get_task_state_core(result) != LEAN_TASK_STATE_FINISHED);
    lean_init_task_manager_using(2);
    CHECK(lean_io_get_task_state_core(result) == LEAN_TASK_STATE_FINISHED);
    if (lean_io_get_task_state_core(result) == LEAN_TASK_STATE_FINISHED)
        CHECK(lean_task_get(result) == lean_box(0));
    CHECK(g_continuation_runs == 0);
    lean_dec(continuation);
    lean_dec(result);
}

static lean_object * wait_for(lean_object * task, lean_object * unit) {
    (void)unit;
    lean_task_get(task);
    lean_dec(task);
    return lean_box(0);
}

/* Expects the task manager to be running, and leaves it running. A hang is turned into a failure by
   `SIGALRM`, after flushing what earlier checks reported. */
static void check_task_waiting_on_kept_promise(void) {
    lean_object * result = pending_timer_result();
    if (result == NULL)
        return;
    lean_finalize_task_manager();
    lean_init_task_manager_using(2);

    lean_object * waiter = lean_alloc_closure((void *)wait_for, 2, 1);
    lean_closure_set(waiter, 0, result);
    lean_object * task = lean_task_spawn_core(waiter, 0, 0);
    fflush(0);
    alarm(120);
    lean_finalize_task_manager();
    alarm(0);
    CHECK(lean_io_get_task_state_core(task) == LEAN_TASK_STATE_FINISHED);
    lean_dec(task);
    lean_init_task_manager_using(2);
}

static _Atomic int g_finalizing = 0;

static lean_object * hold_finalization(lean_object * unit) {
    (void)unit;
    while (!lean_io_check_canceled_core())
        usleep(1000);
    g_finalizing = 1;
    usleep(200000);
    return lean_box(0);
}

static void * finalize_on_thread(void * arg) {
    (void)arg;
    lean_initialize_thread();
    lean_finalize_task_manager();
    lean_finalize_thread();
    return 0;
}

/* Expects the task manager to be running, and leaves it running. */
static void check_restart_during_finalization(void) {
    lean_object * result = pending_timer_result();
    if (result == NULL)
        return;
    int runs = g_continuation_runs;
    lean_inc(result);
    lean_object * continuation = lean_task_map_core(lean_alloc_closure((void *)count_run, 1, 0), result, 0, 1, 0);
    /* Priority 9 is a dedicated thread, which the finalization waits for. */
    lean_object * holder = lean_task_spawn_core(lean_alloc_closure((void *)hold_finalization, 1, 0), 9, 0);

    thread_handle finalizer;
    if (pthread_create(&finalizer, 0, finalize_on_thread, 0) != 0) {
        printf("pthread_create failed\n");
        g_failures++;
        lean_finalize_task_manager();
    } else {
        while (!g_finalizing)
            usleep(1000);
        lean_init_task_manager_using(2);
        pthread_join(finalizer, 0);
    }
    lean_init_task_manager_using(2);

    CHECK(lean_io_get_task_state_core(result) == LEAN_TASK_STATE_FINISHED);
    CHECK(g_continuation_runs == runs);
    CHECK(timer_fires());
    lean_dec(holder);
    lean_dec(continuation);
    lean_dec(result);
}

static _Atomic int g_start_restarting = 0;

static void * restart_on_thread(void * arg) {
    (void)arg;
    lean_initialize_thread();
    while (!g_start_restarting) {}
    lean_init_task_manager_using(2);
    lean_finalize_thread();
    return 0;
}

/* Expects the task manager to be running, and leaves it running. */
static void check_concurrent_restarts(void) {
    enum { num_threads = 4, num_cycles = 100 };
    fflush(0);
    alarm(120);
    for (int cycle = 0; cycle < num_cycles; cycle++) {
        lean_finalize_task_manager();
        g_start_restarting = 0;
        thread_handle threads[num_threads];
        int started = 0;
        for (; started < num_threads; started++) {
            if (pthread_create(&threads[started], 0, restart_on_thread, 0) != 0) {
                printf("pthread_create failed\n");
                g_failures++;
                break;
            }
        }
        g_start_restarting = 1;
        for (int i = 0; i < started; i++)
            pthread_join(threads[i], 0);
        lean_init_task_manager_using(2);
    }
    alarm(0);
    CHECK(timer_fires());
}

static _Atomic int g_stop_calling = 0;

static void * call_into_libuv(void * arg) {
    (void)arg;
    lean_initialize_thread();
    while (!g_stop_calling) {
        lean_object * r = lean_uv_timer_mk(1, 0);
        if (lean_io_result_is_ok(r)) {
            lean_object * next = lean_uv_timer_next(lean_io_result_get_value(r));
            lean_dec(next);
        }
        lean_dec(r);
    }
    lean_finalize_thread();
    return 0;
}

/* Expects the task manager to be running, and leaves it running. A hang is turned into a failure by
   `SIGALRM`, after flushing what earlier checks reported. */
static void check_finalize_while_threads_call_into_libuv(void) {
    enum { num_threads = 4 };
    thread_handle threads[num_threads];
    int started = 0;
    for (; started < num_threads; started++) {
        if (pthread_create(&threads[started], 0, call_into_libuv, 0) != 0) {
            printf("pthread_create failed\n");
            g_failures++;
            break;
        }
    }
    fflush(0);
    alarm(120);
    for (int i = 0; i < 20; i++) {
        usleep(1000);
        lean_finalize_task_manager();
        lean_init_task_manager_using(2);
    }
    alarm(0);
    g_stop_calling = 1;
    for (int i = 0; i < started; i++)
        pthread_join(threads[i], 0);
}

static void exit_during_teardown(void) {
    lean_init_task_manager_using(2);
    /* Each timer hands its object to the teardown, which collects them while the exit handlers run. */
    for (int i = 0; i < 4096; i++) {
        lean_object * timer = take_ok(lean_uv_timer_mk(3600000, 0), "Timer.mk");
        if (timer == NULL)
            return;
        lean_dec(lean_uv_timer_next(timer));
        lean_dec(timer);
    }
    /* Keeps the teardown in `uv_run` until after the exit has started. */
    lean_dec(lean_uv_random(256 * 1024 * 1024));
    usleep(50000);
    thread_handle thread;
    if (pthread_create(&thread, 0, finalize_on_thread, 0) != 0) {
        printf("pthread_create failed\n");
        exit(1);
    }
    /* Still tearing the loop down when the process exits. */
    pthread_detach(thread);
    usleep(100000);
    exit(0);
}

/* `IO.Process.spawn { cmd, args := #[arg] }` with all of stdio inherited, built as `IO.Process.SpawnArgs`. */
static lean_object * spawn(char const * cmd, char const * arg) {
    lean_object * stdio = lean_alloc_ctor(0, 0, 3);
    for (int i = 0; i < 3; i++)
        lean_ctor_set_uint8(stdio, i, 1);
    lean_object * args = lean_alloc_ctor(0, 5, 2);
    lean_ctor_set(args, 0, stdio);
    lean_ctor_set(args, 1, lean_mk_string(cmd));
    lean_ctor_set(args, 2, lean_array_push(lean_mk_empty_array(), lean_mk_string(arg)));
    lean_ctor_set(args, 3, lean_box(0));
    lean_ctor_set(args, 4, lean_mk_empty_array());
    lean_ctor_set_uint8(args, 5 * sizeof(void *), 1);
    lean_ctor_set_uint8(args, 5 * sizeof(void *) + 1, 0);
    return take_ok(lean_io_process_spawn(args), "IO.Process.spawn");
}

static lean_object * g_child;

static lean_object * wait_for_child(lean_object * unit) {
    lean_dec(lean_io_process_child_wait(lean_box(0), g_child));
    return unit;
}

/* Runs on the loop thread. */
static lean_object * wait_for_waiting_task(lean_object * v) {
    lean_dec(v);
    lean_object * task = lean_task_spawn_core(lean_alloc_closure((void *)wait_for_child, 1, 0), 0, false);
    lean_object * list = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(list, 0, task);
    lean_ctor_set(list, 1, lean_box(0));
    lean_io_wait_any_core(list);
    lean_dec(list);
    return lean_box(0);
}

static void wait_exited_child_from_loop(void) {
    g_child = spawn("sleep", "0");
    if (g_child == NULL)
        return;
    lean_dec(lean_io_process_child_wait(lean_box(0), g_child));
    lean_object * timer = take_ok(lean_uv_timer_mk(10, 0), "Timer.mk");
    lean_object * promise = take_ok(lean_uv_timer_next(timer), "Timer.next");
    lean_object * done = lean_task_map_core(lean_alloc_closure((void *)wait_for_waiting_task, 1, 0),
                                            lean_io_promise_result_opt(promise), 0, true, false);
    lean_task_get(done);
    lean_dec(done);
    lean_dec(promise);
    lean_dec(timer);
    lean_dec(g_child);
}

static lean_object * g_wait_result;

static void * wait_on_thread(void * unused) {
    (void)unused;
    lean_initialize_thread();
    g_wait_result = lean_io_process_child_wait(lean_box(0), g_child);
    lean_finalize_thread();
    return 0;
}

static void wait_across_teardown(void) {
    g_child = spawn("sleep", "1");
    if (g_child == NULL)
        return;
    thread_handle thread;
    if (pthread_create(&thread, 0, wait_on_thread, 0) != 0) {
        printf("pthread_create failed\n");
        g_failures++;
        return;
    }
    usleep(200000);
    lean_finalize_task_manager();
    pthread_join(thread, 0);
    CHECK(!lean_io_result_is_ok(g_wait_result));
    lean_dec(g_wait_result);
    lean_init_task_manager_using(2);
    expect_error(lean_io_process_child_try_wait(lean_box(0), g_child), "tryWait on a child the teardown closed");
    lean_dec(g_child);
}

static void zombies(void) {
    for (int i = 0; i < 10; i++) {
        lean_object * child = spawn("sleep", "1");
        if (child == NULL)
            return;
        lean_dec(child);
        lean_finalize_task_manager();
        lean_init_task_manager_using(2);
    }
    usleep(1500000);
    lean_finalize_task_manager();
    lean_init_task_manager_using(2);
    int zombies = 0, status;
    while (waitpid(-1, &status, 1 /* WNOHANG */) > 0)
        zombies++;
    CHECK(zombies == 0);
}

static void failed_restart(void) {
    struct rlimit_ limit;
    getrlimit(RLIMIT_NOFILE_, &limit);
    struct rlimit_ low = {256, limit.max};
    setrlimit(RLIMIT_NOFILE_, &low);
    lean_finalize_task_manager();
    int fds[256], n = 0, fd;
    while (n < 256 && (fd = dup(1)) >= 0)
        fds[n++] = fd;
    lean_init_task_manager_using(2);
    CHECK(!lean_uv_event_loop_alive());
    while (n > 0)
        close(fds[--n]);
    lean_init_task_manager_using(2);
    CHECK(timer_fires());
    setrlimit(RLIMIT_NOFILE_, &limit);
}

static void signal_during_teardown(void) {
    lean_object * signal = take_ok(lean_uv_signal_mk(10 /* SIGUSR1 */, 1), "Signal.mk");
    if (signal == NULL)
        return;
    lean_dec(take_ok(lean_uv_signal_next(signal), "Signal.next"));
    /* Keeps the teardown in `uv_run` after the signal has been sent. */
    lean_dec(lean_uv_random(256 * 1024 * 1024));
    usleep(50000);
    thread_handle thread;
    if (pthread_create(&thread, 0, finalize_on_thread, 0) != 0) {
        printf("pthread_create failed\n");
        g_failures++;
        return;
    }
    usleep(100000);
    kill(getpid(), SIGUSR1_);
    pthread_join(thread, 0);
    lean_dec(signal);
    lean_init_task_manager_using(2);
}

static void finalize_in_finalizer(void * p) {
    (void)p;
    lean_finalize_task_manager();
}

static void no_references(void * p, b_lean_obj_arg f) {
    (void)p;
    (void)f;
}

static void finalize_on_loop_thread(void) {
    lean_external_class * finalizing = lean_register_external_class(finalize_in_finalizer, no_references);
    lean_object * timer = take_ok(lean_uv_timer_mk(50, 0), "Timer.mk");
    lean_object * promise = take_ok(lean_uv_timer_next(timer), "Timer.next");
    /* The loop then holds the last reference to the promise, and so to the value. */
    lean_dec(lean_io_promise_resolve(lean_alloc_external(finalizing, 0), promise));
    lean_dec(promise);
    lean_dec(timer);
    usleep(1000000);
}

/* Each runs with the task manager running, and leaves it running. */
static struct { char const * name; void (*run)(void); } const g_modes[] = {
    {"wait_exited_child_from_loop", wait_exited_child_from_loop},
    {"wait_across_teardown", wait_across_teardown},
    {"zombies", zombies},
    {"failed_restart", failed_restart},
    {"signal_during_teardown", signal_during_teardown},
    {"finalize_on_loop_thread", finalize_on_loop_thread},
};

int main(int argc, char ** argv) {
    lean_initialize_runtime_module();
    if (argc > 1 && strcmp(argv[1], "exit_during_teardown") == 0)
        exit_during_teardown();
    for (unsigned i = 0; argc > 1 && i < sizeof(g_modes) / sizeof(g_modes[0]); i++) {
        if (strcmp(argv[1], g_modes[i].name) != 0)
            continue;
        alarm(60); // turns a hang into a failure
        lean_init_task_manager_using(2);
        g_modes[i].run();
        lean_finalize_task_manager();
        if (g_failures != 0) {
            printf("%d check(s) failed\n", g_failures);
            return 1;
        }
        printf("%s: ok\n", argv[1]);
        return 0;
    }

    lean_init_task_manager_using(2);
    CHECK(timer_fires());
    lean_object * timer = take_ok(lean_uv_timer_mk(10, 0), "Timer.mk");
    lean_object * signal = take_ok(lean_uv_signal_mk(28, 1), "Signal.mk");
    lean_object * socket = take_ok(lean_uv_tcp_new(), "TCP.Socket.new");
    lean_object * udp_socket = take_ok(lean_uv_udp_new(), "UDP.Socket.new");
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
        expect_error(lean_uv_tcp_send(socket, lean_mk_empty_array()), "TCP send of no data on a socket from the previous cycle");
        lean_dec(socket);
    }
    if (udp_socket != NULL) {
        expect_error(lean_uv_udp_send(udp_socket, lean_mk_empty_array(), lean_box(0)),
                     "UDP send of no data on a socket from the previous cycle");
        lean_dec(udp_socket);
    }
    lean_finalize_task_manager();

    lean_init_task_manager_using(2);
    CHECK(timer_fires());
    check_pending_promise_released_at_restart();
    check_task_waiting_on_kept_promise();
    check_restart_during_finalization();
    check_concurrent_restarts();
    check_finalize_while_threads_call_into_libuv();
    CHECK(timer_fires());
    lean_finalize_task_manager();

    if (g_failures != 0) {
        printf("%d check(s) failed\n", g_failures);
        return 1;
    }
    return 0;
}
