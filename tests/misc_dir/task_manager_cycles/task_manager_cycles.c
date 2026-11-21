/*
Tests of the task manager across `lean_finalize_task_manager`, as an embedder that finalizes and
re-initializes it sees it, and of work that becomes runnable once it has stopped running tasks.

* The task manager can be finalized and started again, and a promise left pending in one cycle can
  be resolved in the next.
* Between cycles, dropping a promise that has dependents, mapping over a task and spawning one do
  not crash, and nothing is run that the stopped manager discarded.
* A dependent dropped between cycles is not run in a later cycle.
* A drop that discards work that holds the last reference to another pending promise discards that
  promise's dependents too, and a map over a discarded task is discarded at once.
* `lean_finalize_task_manager` waits for a `(sync := true)` task that a thread it does not own is
  running, so the task that one spawns and waits for still runs.
* `lean_finalize_task_manager` does not wait for a thread it does not own that waits for a pending
  promise, and the promise can still be resolved afterwards.
* Ten cycles, each stopping with different work in flight (running, queued and dedicated tasks,
  late work waited for or not, promises resolved, dropped or carried into the next cycle, a chain,
  `(sync := true)` dependents, a foreign thread), free every closure and run what is running or
  waited for.
* With the argument `finalize_from_task`, finalizing from a task fails with an internal panic
  instead of waiting for that task forever.

Each test can be run alone by passing its name. Leaks are reported in the sanitize build. Threads are
created with POSIX threads, so the test does not run on Windows.
*/
#include <lean/lean.h>

// `leanc` ships no C library headers, but links the C library.
int printf(char const * fmt, ...);
int strcmp(char const * a, char const * b);
int usleep(unsigned int usec);
void * malloc(size_t size);
void free(void * p);
// `pthread_t` is a pointer-sized integer or pointer on the platforms this test runs on.
typedef unsigned long long thread_handle;
int pthread_create(thread_handle * thread, void const * attr, void * (*start)(void *), void * arg);
int pthread_join(thread_handle thread, void ** result);

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_object * lean_io_promise_new(void);
lean_object * lean_io_promise_resolve(lean_object * value, lean_object * promise);
lean_object * lean_io_promise_result_opt(lean_object * promise);

/* `Task.Priority.dedicated` */
#define LEAN_DEDICATED_PRIO 9

static int g_failures = 0;

#define CHECK(c) do { \
    if (!(c)) { printf("%s:%d: check failed: %s\n", __FILE__, __LINE__, #c); g_failures++; } \
} while (0)

static _Atomic int g_ran_dropped = 0;
static _Atomic int g_ran_discarded = 0;
static _Atomic int g_ran_kept = 0;
static _Atomic int g_ran_inline = 0;

static lean_object * count_dropped(lean_object * v) {
    lean_dec(v);
    g_ran_dropped++;
    return lean_box(0);
}

static lean_object * count_discarded(lean_object * v) {
    lean_dec(v);
    g_ran_discarded++;
    return lean_box(0);
}

static lean_object * count_kept(lean_object * v) {
    lean_dec(v);
    g_ran_kept++;
    return lean_box(0);
}

static lean_object * count_inline(lean_object * unit) {
    (void)unit;
    g_ran_inline++;
    return lean_box(7);
}

/* A dependent whose closure holds the last reference to `promise`. */
static lean_object * holds_promise(lean_object * promise, lean_object * v) {
    lean_dec(promise);
    lean_dec(v);
    g_ran_discarded++;
    return lean_box(0);
}

static lean_object * fn1(lean_object * (*f)(lean_object *)) {
    return lean_alloc_closure((void *)f, 1, 0);
}

static lean_object * map(lean_object * (*f)(lean_object *), lean_object * task, bool keep_alive) {
    return lean_task_map_core(fn1(f), task, 0, false, keep_alive);
}

static void resolve(lean_object * promise) {
    lean_dec(lean_io_promise_resolve(lean_box(1), promise));
}

/* A finished cycle followed by a new one. */
static void test_restart(void) {
    lean_init_task_manager_using(4);
    lean_object * spawned = lean_task_spawn_core(fn1(count_inline), 0, false);
    CHECK(lean_task_get(spawned) == lean_box(7));
    lean_dec(spawned);
    lean_finalize_task_manager();
    lean_init_task_manager_using(4);
    spawned = lean_task_spawn_core(fn1(count_inline), 0, false);
    CHECK(lean_task_get(spawned) == lean_box(7));
    lean_dec(spawned);
    lean_finalize_task_manager();
    CHECK(g_ran_inline == 2);
}

/* A promise left pending in one cycle is resolved in the next, and its dependent runs there. */
static void test_carry_over(void) {
    lean_init_task_manager_using(4);
    lean_object * kept = lean_io_promise_new();
    lean_object * kept_dependent = map(count_kept, lean_io_promise_result_opt(kept), false);
    lean_finalize_task_manager();
    lean_init_task_manager_using(4);
    resolve(kept);
    lean_object * kept_result = lean_io_promise_result_opt(kept);
    CHECK(lean_unbox(lean_ctor_get(lean_task_get(kept_result), 0)) == 1);
    lean_dec(kept_result);
    lean_task_get(kept_dependent);
    lean_finalize_task_manager();
    CHECK(g_ran_kept == 1);
    lean_dec(kept_dependent);
    lean_dec(kept);
}

/* 15743-01: dropping a pending promise between cycles resolves it, and its dependent is discarded. */
static void test_gap_drop_promise(void) {
    lean_init_task_manager_using(4);
    lean_object * promise = lean_io_promise_new();
    lean_object * dependent = map(count_discarded, lean_io_promise_result_opt(promise), true);
    lean_finalize_task_manager();
    lean_dec(promise);
    // A discarded task never finishes.
    CHECK(lean_io_get_task_state_core(dependent) == LEAN_TASK_STATE_RUNNING);
    lean_dec(dependent);
    CHECK(g_ran_discarded == 0);
}

/* 15743-01: between cycles, spawning and mapping over a finished task run inline. */
static void test_gap_spawn_map(void) {
    lean_init_task_manager_using(4);
    lean_finalize_task_manager();
    lean_object * spawned = lean_task_spawn_core(fn1(count_inline), 0, false);
    CHECK(g_ran_inline == 1 && lean_task_get(spawned) == lean_box(7));
    lean_object * mapped = lean_task_map_core(fn1(count_inline), spawned, 0, false, false);
    CHECK(g_ran_inline == 2 && lean_task_get(mapped) == lean_box(7));
    lean_dec(mapped);
}

/* 15743-01: between cycles, a map over a pending promise's result is linked, and runs once the next
   cycle resolves the promise. */
static void test_gap_map_pending(void) {
    lean_init_task_manager_using(4);
    lean_object * promise = lean_io_promise_new();
    lean_finalize_task_manager();
    lean_object * dependent = map(count_kept, lean_io_promise_result_opt(promise), false);
    lean_init_task_manager_using(4);
    resolve(promise);
    lean_task_get(dependent);
    lean_finalize_task_manager();
    CHECK(g_ran_kept == 1);
    lean_dec(dependent);
    lean_dec(promise);
}

/* 15743-02: a dependent dropped between cycles is not run when the next cycle resolves its promise. */
static void test_gap_drop_dependent(void) {
    lean_init_task_manager_using(4);
    lean_object * promise = lean_io_promise_new();
    lean_object * dependent = map(count_dropped, lean_io_promise_result_opt(promise), false);
    lean_finalize_task_manager();
    lean_dec(dependent);
    lean_init_task_manager_using(4);
    lean_dec(promise);
    lean_finalize_task_manager();
    CHECK(g_ran_dropped == 0);
}

/* Discarding with nesting, and a map over a discarded task. */
static void test_discard_after_stop(void) {
    lean_init_task_manager_using(4);
    lean_object * outer = lean_io_promise_new();
    lean_object * inner = lean_io_promise_new();
    lean_dec(map(count_discarded, lean_io_promise_result_opt(inner), true));
    lean_object * f = lean_alloc_closure((void *)holds_promise, 2, 1);
    lean_closure_set(f, 0, inner);
    lean_object * holder = lean_task_map_core(f, lean_io_promise_result_opt(outer), 0, false, false);
    lean_finalize_task_manager();

    lean_dec(outer);
    CHECK(lean_io_get_task_state_core(holder) == LEAN_TASK_STATE_RUNNING);
    lean_inc(holder);
    lean_object * after = map(count_discarded, holder, false);
    CHECK(lean_io_get_task_state_core(after) == LEAN_TASK_STATE_RUNNING);
    lean_dec(after);
    lean_dec(holder);
    CHECK(g_ran_discarded == 0);
}

static _Atomic int g_foreign_waiting = 0;

static void * wait_on_foreign_thread(void * result) {
    lean_initialize_thread();
    g_foreign_waiting = 1;
    lean_task_get((lean_object *)result);
    lean_finalize_thread();
    return 0;
}

/* A thread the task manager does not own, waiting for a pending promise, does not hold
   `lean_finalize_task_manager` up, and the promise can still be resolved afterwards. */
static void test_finalize_ignores_foreign_waiter(void) {
    lean_init_task_manager_using(4);
    lean_object * promise = lean_io_promise_new();
    lean_object * result = lean_io_promise_result_opt(promise);
    thread_handle thread;
    CHECK(pthread_create(&thread, 0, wait_on_foreign_thread, result) == 0);
    while (!g_foreign_waiting)
        usleep(1000);
    lean_finalize_task_manager();
    resolve(promise);
    pthread_join(thread, 0);
    lean_dec(result);
    lean_dec(promise);
}

static _Atomic int g_sync_started = 0;
static _Atomic int g_sync_done = 0;

static lean_object * spawned_value(lean_object * unit) {
    (void)unit;
    return lean_box(3);
}

/* Spawns a task once the exit has started, and waits for it. `lean_task_get` is not allowed in a
   `(sync := true)` task, `IO.waitAny` is. */
static lean_object * straddling_continuation(lean_object * v) {
    lean_dec(v);
    g_sync_started = 1;
    usleep(200 * 1000);
    lean_object * t = lean_task_spawn_core(fn1(spawned_value), 0, false);
    lean_object * list = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(list, 0, t);
    lean_ctor_set(list, 1, lean_box(0));
    lean_io_wait_any_core(list);
    lean_dec(list);
    g_sync_done = 1;
    return lean_box(0);
}

static void * resolve_on_foreign_thread(void * promise) {
    lean_initialize_thread();
    resolve((lean_object *)promise);
    lean_finalize_thread();
    return 0;
}

/* C-1: a `(sync := true)` task running on a thread the task manager does not own when it is
   finalized. */
static void test_finalize_waits_for_foreign_sync_task(void) {
    lean_init_task_manager_using(4);
    lean_object * promise = lean_io_promise_new();
    lean_object * dependent = lean_task_map_core(fn1(straddling_continuation), lean_io_promise_result_opt(promise), 0, true, false);
    thread_handle thread;
    CHECK(pthread_create(&thread, 0, resolve_on_foreign_thread, promise) == 0);
    while (!g_sync_started)
        usleep(1000);
    lean_finalize_task_manager();
    CHECK(g_sync_done == 1);
    if (g_sync_done != 1)
        // The thread waits forever for a task the stopped manager discarded.
        return;
    pthread_join(thread, 0);
    lean_dec(dependent);
    lean_dec(promise);
}

/* restart_mixed: every closure owns an external object, counted when created and when freed. */
static lean_external_class * g_counted_class;
static _Atomic long g_created = 0;
static _Atomic long g_freed = 0;
static _Atomic int g_ran_mixed = 0;
static int g_cycle;
static lean_object * g_drop;   /* a promise that the exit-time task drops or resolves */
static lean_object * g_carry;  /* a promise left pending from one cycle to the next */
static _Atomic int g_carry_ran = 0;

static void counted_finalize(void * p) { free(p); g_freed++; }
static void counted_foreach(void * p, b_lean_obj_arg f) { (void)p; (void)f; }
static lean_object * counted(void) { g_created++; return lean_alloc_external(g_counted_class, malloc(16)); }

static lean_object * owns_fn(lean_object * e, lean_object * v) { lean_dec(e); lean_dec(v); g_ran_mixed++; return lean_box(0); }
static lean_object * sleeps_fn(lean_object * e, lean_object * v) { usleep(20 * 1000); return owns_fn(e, v); }
static lean_object * carry_fn(lean_object * e, lean_object * v) { g_carry_ran++; return owns_fn(e, v); }
static lean_object * closure_with(void * f) { lean_object * c = lean_alloc_closure(f, 2, 1); lean_closure_set(c, 0, counted()); return c; }
static lean_object * spawn_owning(void * f, unsigned prio, bool keep_alive) { return lean_task_spawn_core(closure_with(f), prio, keep_alive); }
static lean_object * map_owning(lean_object * t, bool sync, bool keep_alive) { return lean_task_map_core(closure_with((void *)owns_fn), t, 0, sync, keep_alive); }

/* Waits until the task manager is stopping, then starts this cycle's exit-time work. Runs on a dedicated thread. */
static lean_object * at_exit(lean_object * unit) {
    (void)unit;
    while (!lean_io_check_canceled_core())
        usleep(100);
    switch (g_cycle) {
    case 3:  /* pool tasks that nothing waits for */
        for (int i = 0; i < 20; i++) lean_dec(spawn_owning((void *)owns_fn, (unsigned)(i % 3), true));
        break;
    case 4: { /* a pool task this task waits for */
        lean_object * t = spawn_owning((void *)owns_fn, 0, false);
        lean_task_get(t);
        lean_dec(t);
        break;
    }
    case 5:  /* resolves the promise a pool task is blocked on, through a map */
    case 8:  /* resolves a promise with `(sync := true)` dependents, which run here */
        resolve(g_drop);
        lean_dec(g_drop);
        g_drop = NULL;
        break;
    case 6:  /* drops a pending promise with dependents */
        lean_dec(g_drop);
        g_drop = NULL;
        break;
    case 7: { /* a chain of 1000 maps on a new pool task */
        lean_object * t = spawn_owning((void *)owns_fn, 0, false);
        for (int i = 0; i < 1000; i++) t = map_owning(t, false, false);
        lean_dec(t);
        break;
    }
    }
    return lean_box(0);
}

static lean_object * blocked_on_map(lean_object * map_task, lean_object * unit) {
    (void)unit;
    lean_task_get(map_task);
    lean_dec(map_task);
    g_ran_mixed++;
    return lean_box(0);
}

static void * resolve_drop_late(void * unused) {
    (void)unused;
    lean_initialize_thread();
    usleep(1000);
    resolve(g_drop);
    lean_dec(g_drop);
    g_drop = NULL;
    lean_finalize_thread();
    return 0;
}

/* Ten init/finalize cycles, each with different work in flight when the task manager stops. Work that runs, is
   waited for, or is discarded must all be freed (also checked by LeakSanitizer in the sanitize build), and work that
   is running or waited for must run. */
static void test_restart_mixed(void) {
    if (!g_counted_class)
        g_counted_class = lean_register_external_class(counted_finalize, counted_foreach);
    g_created = g_freed = 0;
    for (g_cycle = 0; g_cycle < 10; g_cycle++) {
        lean_init_task_manager_using(1 + g_cycle % 4);
        g_ran_mixed = 0;
        int expect_ran = -1;
        thread_handle thread = 0;
        switch (g_cycle) {
        case 0:  /* pool tasks still running or queued */
            for (int i = 0; i < 8; i++) lean_dec(spawn_owning((void *)sleeps_fn, 0, true));
            expect_ran = 8;
            break;
        case 1:  /* more queued pool tasks than workers (2) */
            for (int i = 0; i < 6; i++) lean_dec(spawn_owning((void *)sleeps_fn, (unsigned)(i % 2), true));
            expect_ran = 6;
            break;
        case 2:  /* dedicated tasks still running */
            for (int i = 0; i < 3; i++) lean_dec(spawn_owning((void *)sleeps_fn, LEAN_DEDICATED_PRIO, true));
            expect_ran = 3;
            break;
        case 4:
            expect_ran = 1;
            break;
        case 5: { /* a pool task blocked on a map of a promise resolved during the exit */
            g_drop = lean_io_promise_new();
            lean_object * m = map_owning(lean_io_promise_result_opt(g_drop), false, false);
            lean_object * c = lean_alloc_closure((void *)blocked_on_map, 2, 1);
            lean_closure_set(c, 0, m);
            lean_dec(lean_task_spawn_core(c, 0, true));
            expect_ran = 2;
            break;
        }
        case 6:  /* a promise dropped during the exit, and one left pending for the next cycle */
            g_drop = lean_io_promise_new();
            for (int i = 0; i < 10; i++) lean_dec(map_owning(lean_io_promise_result_opt(g_drop), false, i % 2 == 0));
            g_carry = lean_io_promise_new();
            lean_dec(lean_task_map_core(closure_with((void *)carry_fn), lean_io_promise_result_opt(g_carry), 0, false, true));
            break;
        case 7:  /* the promise left pending resolves in this cycle */
            resolve(g_carry);
            while (!g_carry_ran)
                usleep(1000);
            break;
        case 8:
            g_drop = lean_io_promise_new();
            for (int i = 0; i < 10; i++) lean_dec(map_owning(lean_io_promise_result_opt(g_drop), true, true));
            expect_ran = 10;
            break;
        case 9:  /* a thread the task manager does not own resolves a promise around the exit */
            g_drop = lean_io_promise_new();
            for (int i = 0; i < 10; i++) lean_dec(map_owning(lean_io_promise_result_opt(g_drop), false, true));
            CHECK(pthread_create(&thread, 0, resolve_drop_late, NULL) == 0);
            break;
        }
        if (g_cycle >= 3 && g_cycle <= 8)
            lean_dec(lean_task_spawn_core(fn1(at_exit), LEAN_DEDICATED_PRIO, true));
        lean_finalize_task_manager();
        if (thread)
            pthread_join(thread, 0);
        if (expect_ran >= 0 && g_ran_mixed != expect_ran) {
            printf("restart_mixed: cycle %d ran %d of %d\n", g_cycle, (int)g_ran_mixed, expect_ran);
            g_failures++;
        }
        /* The promise carried into cycle 7 keeps its dependent alive until then. */
        long carried = g_cycle == 6 ? 1 : 0;
        if (g_freed + carried != g_created) {
            printf("restart_mixed: cycle %d freed %ld of %ld\n", g_cycle, (long)g_freed, (long)g_created - carried);
            g_failures++;
        }
    }
    lean_dec(g_carry);
    CHECK(g_carry_ran == 1);
}

static lean_object * finalize_from_task(lean_object * unit) {
    (void)unit;
    lean_finalize_task_manager();
    return lean_box(0);
}

static struct { char const * name; void (*run)(void); } const g_tests[] = {
    {"restart", test_restart},
    {"carry_over", test_carry_over},
    {"gap_drop_promise", test_gap_drop_promise},
    {"gap_spawn_map", test_gap_spawn_map},
    {"gap_map_pending", test_gap_map_pending},
    {"gap_drop_dependent", test_gap_drop_dependent},
    {"discard_after_stop", test_discard_after_stop},
    {"foreign_sync_task", test_finalize_waits_for_foreign_sync_task},
    {"foreign_waiter", test_finalize_ignores_foreign_waiter},
    {"restart_mixed", test_restart_mixed},
};

/* Runs the test named by the argument, or all of them in order. */
int main(int argc, char ** argv) {
    lean_initialize_runtime_module();
    if (argc > 1 && strcmp(argv[1], "finalize_from_task") == 0) {
        lean_init_task_manager_using(4);
        lean_object * t = lean_task_spawn_core(fn1(finalize_from_task), 0, false);
        lean_task_get(t);
        printf("finalizing from a task returned\n");
        return 0;
    }
    int found = 0;
    for (unsigned i = 0; i < sizeof(g_tests) / sizeof(g_tests[0]); i++) {
        if (argc > 1 && strcmp(argv[1], g_tests[i].name) != 0)
            continue;
        found = 1;
        g_ran_dropped = g_ran_discarded = g_ran_kept = g_ran_inline = 0;
        g_tests[i].run();
    }
    if (!found) {
        printf("unknown test %s\n", argv[1]);
        return 2;
    }
    if (g_failures != 0) {
        printf("%d check(s) failed\n", g_failures);
        return 1;
    }
    return 0;
}
