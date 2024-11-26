/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
*/
#include <pthread.h>

#include "runtime/libuv.h"

#include "runtime/object.h"

#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN#include <uv.h>

using namespace lean;

uv_loop_t * global_uv_loop;
uv_async_t * global_uv_signal_async;
uv_mutex_t * global_uv_mutex;

uv_cond_t * global_uv_cond;

_Atomic(uint64_t) global_uv_n_waiters(0);

static void lean_uv_wake() {
    uv_async_send(global_uv_signal_async);
}

static void lean_uv_lock() {
    if (uv_mutex_trylock(global_uv_mutex) != 0) {
        global_uv_n_waiters++;
        __sync_synchronize();
        lean_uv_wake();

        uv_mutex_lock(global_uv_mutex);

        global_uv_n_waiters--;
    }
}

static void lean_uv_unlock() {
    if (uv_mutex_trylock(global_uv_mutex) != 0) {
        uv_mutex_unlock(global_uv_mutex);
    }

    if (global_uv_n_waiters == 0) {
        uv_cond_signal(global_uv_cond);
    }
}

static void lean_uv_run() {
    while (1) {
        uv_mutex_lock(global_uv_mutex);

        if (global_uv_n_waiters != 0) {
            uv_cond_wait(global_uv_cond, global_uv_mutex);
        }

        if (global_uv_n_waiters == 0) {
            uv_run(global_uv_loop, UV_RUN_ONCE);
        }

        uv_mutex_unlock(global_uv_mutex);
    }
}

// Bindings

static void lean_uv_timer_finalizer(void * ptr) {
    lean_uv_timer_object * timer_obj = (lean_uv_timer_object * ) ptr;

    if (timer_obj -> m_promise == NULL) {
        uv_close((uv_handle_t * ) & timer_obj -> m_uv_timer, [](uv_handle_t * handle) {
            free(lean_to_uv_timer((lean_object * ) handle -> data));
        });
    }
}

extern "C" lean_obj_res lean_uv_initialize() {
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, noop_foreach);

    global_uv_loop = uv_default_loop();
    global_uv_signal_async = (uv_async_t * ) malloc(sizeof(uv_async_t));
    global_uv_mutex = (uv_mutex_t * ) malloc(sizeof(uv_mutex_t));
    global_uv_cond = (uv_cond_t * ) malloc(sizeof(uv_cond_t));

    if (global_uv_loop == NULL) lean_internal_panic("failed to initialize uv_loop");

    int result = uv_async_init(global_uv_loop, global_uv_signal_async, [](uv_async_t * hdl) {
        uv_stop(global_uv_loop);
    });

    result = uv_mutex_init(global_uv_mutex);
    if (result != 0) lean_internal_panic("failed to initialize uv_mutex");

    result = uv_cond_init(global_uv_cond);
    if (result != 0) lean_internal_panic("failed to initialize uv_cond");

    lthread([]() {
        lean_uv_run();
    });

    return lean_io_result_mk_ok(lean_box(0));
}

using namespace lean;

uv_loop_t * global_uv_loop;
uv_async_t * global_uv_signal_async;
uv_mutex_t * global_uv_mutex;

uv_cond_t * global_uv_cond;

_Atomic(uint64_t) global_uv_n_waiters(0);

static void lean_uv_wake() {
    uv_async_send(global_uv_signal_async);
}

static void lean_uv_lock() {
    if (uv_mutex_trylock(global_uv_mutex) != 0) {
        global_uv_n_waiters++;
        __sync_synchronize();
        lean_uv_wake();

        uv_mutex_lock(global_uv_mutex);

        global_uv_n_waiters--;
    }
}

static void lean_uv_unlock() {
    if (uv_mutex_trylock(global_uv_mutex) != 0) {
        uv_mutex_unlock(global_uv_mutex);
    }

    if (global_uv_n_waiters == 0) {
        uv_cond_signal(global_uv_cond);
    }
}

static void lean_uv_run() {
    while (1) {
        uv_mutex_lock(global_uv_mutex);

        if (global_uv_n_waiters != 0) {
            uv_cond_wait(global_uv_cond, global_uv_mutex);
        }

        if (global_uv_n_waiters == 0) {
            uv_run(global_uv_loop, UV_RUN_ONCE);
        }

        uv_mutex_unlock(global_uv_mutex);
    }
}

// Bindings

static void lean_uv_timer_finalizer(void * ptr) {
    lean_uv_timer_object * timer_obj = (lean_uv_timer_object * ) ptr;

    if (timer_obj -> m_promise == NULL) {
        uv_close((uv_handle_t * ) & timer_obj -> m_uv_timer, [](uv_handle_t * handle) {
            free(lean_to_uv_timer((lean_object * ) handle -> data));
        });
    }
}

extern "C" lean_obj_res lean_uv_initialize() {
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, noop_foreach);

    global_uv_loop = uv_default_loop();
    global_uv_signal_async = (uv_async_t * ) malloc(sizeof(uv_async_t));
    global_uv_mutex = (uv_mutex_t * ) malloc(sizeof(uv_mutex_t));
    global_uv_cond = (uv_cond_t * ) malloc(sizeof(uv_cond_t));

    if (global_uv_loop == NULL) lean_internal_panic("failed to initialize uv_loop");

    int result = uv_async_init(global_uv_loop, global_uv_signal_async, [](uv_async_t * hdl) {
        uv_stop(global_uv_loop);
    });

    result = uv_mutex_init(global_uv_mutex);
    if (result != 0) lean_internal_panic("failed to initialize uv_mutex");

    result = uv_cond_init(global_uv_cond);
    if (result != 0) lean_internal_panic("failed to initialize uv_cond");

    lthread([]() {
        lean_uv_run();
    });

    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

/* UV.Loop.configure (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ ) {
    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    lean_uv_lock();

    if (accum && uv_loop_configure(global_uv_loop, UV_METRICS_IDLE_TIME) != 0) {
        return io_result_mk_error("failed to configure global_uv_loop with UV_METRICS_IDLE_TIME");
    }

    #if!defined(WIN32) && !defined(_WIN32)
    if (block && uv_loop_configure(global_uv_loop, UV_LOOP_BLOCK_SIGNAL, SIGPROF) != 0) {
        return io_result_mk_error("failed to configure global_uv_loop with UV_LOOP_BLOCK_SIGNAL");
    }
    #endif

    lean_uv_unlock();

    return lean_io_result_mk_ok(lean_box(0));
}

/* UV.Loop.alive : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ ) {
    lean_uv_lock();
    int is_alive = uv_loop_alive(global_uv_loop);
    lean_uv_unlock();

    return lean_io_result_mk_ok(lean_box(is_alive));
}

/* UV.Loop.now : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_now(obj_arg /* w */ ) {
    lean_uv_lock();
    uint64_t now = uv_now(global_uv_loop);
    lean_uv_unlock();

    return lean_io_result_mk_ok(lean_box_uint64(now));
}

/* UV.Timer.mk (timeout : UInt64) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, obj_arg /* w */ ) {
    lean_uv_timer_object * timer_obj = (lean_uv_timer_object * ) malloc(sizeof(lean_uv_timer_object));

    lean_uv_lock();
    int result = uv_timer_init(global_uv_loop, & timer_obj -> m_uv_timer);
    lean_uv_unlock();

    timer_obj -> m_promise = NULL;
    timer_obj -> m_timeout = timeout;

    if (result != 0) {
        free(timer_obj);
        return io_result_mk_error("failed to initialize uv_timer");
    }

    lean_object * obj = lean_uv_timer_new(timer_obj);
    timer_obj -> m_uv_timer.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */ ) {
    lean_uv_timer_object * timer_obj = lean_to_uv_timer(timer);

    lean_object * promise_res = lean_io_promise_new(lean_io_mk_world());
    lean_object * promise = lean_ctor_get(promise_res, 0);

    if (timer_obj -> m_promise != NULL) {
        lean_dec(timer_obj -> m_promise);
    }

    timer_obj -> m_promise = promise;

    // Assumes that the event loop has ownership of the promise too!
    lean_inc(timer_obj -> m_promise);
    lean_inc(timer);

    auto on_timer = [](uv_timer_t * handle) {
        lean_object * obj = (lean_object * ) handle -> data;
        lean_uv_timer_object * timer_obj = lean_to_uv_timer(obj);

        if (timer_obj -> m_promise != NULL) {
            lean_io_promise_resolve(lean_box(0), timer_obj -> m_promise, lean_io_mk_world());
            lean_dec(timer_obj -> m_promise);
            timer_obj -> m_promise = NULL;
            uv_timer_stop( & timer_obj -> m_uv_timer);
            lean_dec(obj);
        }
    };

    lean_uv_lock();
    int result = uv_timer_start( & timer_obj -> m_uv_timer, on_timer, timer_obj -> m_timeout, 0);
    lean_uv_unlock();

    if (result != 0) return io_result_mk_error("failed to start uv_timer");

    return lean_io_result_mk_ok(promise);
}

/* UV.Timer.stop (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */ ) {
    lean_uv_timer_object * timer_obj = lean_to_uv_timer(timer);

    lean_uv_lock();
    int result = uv_timer_stop( & timer_obj -> m_uv_timer);
    lean_uv_unlock();

    if (result != 0) return io_result_mk_error("failed to stop uv_timer");

    if (timer_obj -> m_promise != NULL) {
        lean_dec(timer_obj -> m_promise);
        timer_obj -> m_promise = NULL;
    };

    return lean_io_result_mk_ok(lean_box(0));
}

#else

extern "C"
lean_obj_res lean_uv_initialize() {
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_event_loop_configure is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_event_loop_alive is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_now(obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_event_loop_now is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_timer_mk is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_timer_next is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_timer_stop is not supported");
}

#endif
