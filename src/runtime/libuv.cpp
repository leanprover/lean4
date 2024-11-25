/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
*/
#include "runtime/libuv.h"
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

using namespace lean;

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

static void stop_handles(uv_handle_t* handle_ptr, void* arg) {
    if (uv_is_closing(handle_ptr)) return;

    switch (handle_ptr->type) {
    case UV_TIMER: {
        lean_object* obj = (lean_object*) handle_ptr->data;
        lean_uv_timer_object* handle = lean_to_uv_timer(obj);

        if (handle->m_promise != NULL) {
            lean_dec(handle->m_promise);
            handle->m_promise = NULL;
        }

        lean_dec(obj);
        return;
    }
    default:
        lean_internal_panic("Unsupported handle type");
        break;
    }
}

static void lean_uv_event_loop_finalizer(void* ptr) {
    lean_uv_event_loop_object* loop_obj = (lean_uv_event_loop_object*) ptr;
    uv_loop_t* loop = &loop_obj->m_uv_loop;
    int result = uv_loop_close(loop);

    if (result == UV_EBUSY) {
        uv_walk(loop, &stop_handles, NULL);

        // Run it again to check if there are active handles after closing.
        result = uv_run(loop, UV_RUN_DEFAULT);
        if (result != 0) lean_internal_panic("libuv cannot close the loop failed tried to run again.");

        result = uv_loop_close(loop);
        if (result != 0) lean_internal_panic("libuv cannot close the loop failed.");

    }

    if (result == 0) {
        free(ptr);
    } else {
        lean_internal_panic("libuv returned unexpected error code.");
    }
}

static void lean_uv_timer_finalizer(void* ptr) {
    lean_uv_timer_object* timer_obj = (lean_uv_timer_object*) ptr;

    if (timer_obj->m_promise == NULL) {
        uv_close((uv_handle_t*)&timer_obj->m_uv_timer, [](uv_handle_t* handle) { free(lean_to_uv_timer((lean_object*)handle->data)); });
    }
}

extern "C" lean_obj_res lean_uv_initialize() {
    g_uv_event_loop_external_class = lean_register_external_class(lean_uv_event_loop_finalizer, noop_foreach);
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, noop_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}

/* UV.EventLoop.mk : IO EventLoop */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_mk(obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = (lean_uv_event_loop_object*)malloc(sizeof(lean_uv_event_loop_object));
    int result = uv_loop_init(&loop_obj->m_uv_loop);
    lean_object* obj = lean_uv_event_loop_new(loop_obj);
    loop_obj->m_uv_loop.data = obj;

    if (result != 0) {
        free(loop_obj);
        return io_result_mk_error("failed to initialize uv_loop");
    }

    return lean_io_result_mk_ok(obj);
}

/* UV.Timer.run (loop : @& EventLoop) (runMode : RunMode) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_run(b_obj_arg loop, uint8_t mode, obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    int result = uv_run(&loop_obj->m_uv_loop, (uv_run_mode)mode);

    if (result != 0) {
        free(loop_obj);
        return io_result_mk_error("failed to run uv_loop");
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* UV.Timer.configure (loop : @& EventLoop) (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg loop, b_obj_arg options, obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    uv_loop_t*  uv_loop = &loop_obj->m_uv_loop;

    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    if (accum && uv_loop_configure(uv_loop, UV_METRICS_IDLE_TIME) != 0) {
        return io_result_mk_error("failed to configure uv_loop with UV_METRICS_IDLE_TIME");
    }

    #if !defined(WIN32) && !defined(_WIN32)
    if (block && uv_loop_configure(uv_loop, UV_LOOP_BLOCK_SIGNAL, SIGPROF) != 0) {
        return io_result_mk_error("failed to configure uv_loop with UV_LOOP_BLOCK_SIGNAL");
    }
    #endif

    return lean_io_result_mk_ok(lean_box(0));
}

/* UV.Timer.close (loop : @& EventLoop) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_close(b_obj_arg loop, obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    int result = uv_loop_close(&loop_obj->m_uv_loop);

    if (result != 0) {
        return io_result_mk_error("failed to close uv_loop");
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* UV.Timer.stop (loop : @& EventLoop) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_stop(b_obj_arg loop, obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    uv_stop(&loop_obj->m_uv_loop);

    return lean_io_result_mk_ok(lean_box(0));
}

/* UV.Timer.alive (loop : @& EventLoop) : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(b_obj_arg loop, obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    int is_alive = uv_loop_alive(&loop_obj->m_uv_loop);

    return lean_io_result_mk_ok(lean_box(is_alive));
}

/* UV.Timer.now (loop : @& EventLoop) : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_now(b_obj_arg loop, obj_arg /* w */) {
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    uint64_t now = uv_now(&loop_obj->m_uv_loop);

    return lean_io_result_mk_ok(lean_box_uint64(now));
}

/* UV.Timer.mk (loop : @& EventLoop) (timeout : UInt64) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(b_obj_arg loop, uint64_t timeout, obj_arg /* w */) {
    lean_uv_timer_object* timer_obj = (lean_uv_timer_object*)malloc(sizeof(lean_uv_timer_object));
    lean_uv_event_loop_object* loop_obj = lean_to_uv_event_loop(loop);
    int result = uv_timer_init(&loop_obj->m_uv_loop, &timer_obj->m_uv_timer);

    timer_obj->m_promise = NULL;
    timer_obj->m_timeout = timeout;

    if (result != 0) {
        free(timer_obj);
        return io_result_mk_error("failed to initialize uv_timer");
    }

    lean_object* obj = lean_uv_timer_new(timer_obj);
    timer_obj->m_uv_timer.data = obj;

    /// The timer lives as much as the loop lives... if the loop dies it tried to kill the timer, if the timer dies
    // it tries to kill the loop
    lean_inc(loop);
    return lean_io_result_mk_ok(obj);
}

/* UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */) {
    lean_uv_timer_object* timer_obj = lean_to_uv_timer(timer);

    lean_object* promise_res = lean_io_promise_new(lean_io_mk_world());
    lean_object* promise = lean_ctor_get(promise_res, 0);
    
    if(timer_obj->m_promise != NULL) {
        lean_dec(timer_obj->m_promise);
    }

    timer_obj->m_promise = promise;

    // Assumes that the event loop has ownership of the promise too!
    lean_inc(timer_obj->m_promise);

    auto on_timer = [](uv_timer_t* handle) {
        lean_object* obj = (lean_object*)handle->data;
        lean_uv_timer_object* timer_obj = lean_to_uv_timer(obj);

        if (timer_obj->m_promise != NULL) {
            lean_io_promise_resolve(lean_box(0), timer_obj->m_promise, lean_io_mk_world());
            lean_dec(timer_obj->m_promise);
            timer_obj->m_promise = NULL;
            uv_timer_stop(&timer_obj->m_uv_timer);
        }
    };

    int result = uv_timer_start(&timer_obj->m_uv_timer, on_timer, timer_obj->m_timeout, 0);
    if (result != 0) return io_result_mk_error("failed to start uv_timer");

    return lean_io_result_mk_ok(promise);
}

/* UV.Timer.stop (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */) {
    lean_uv_timer_object* timer_obj = lean_to_uv_timer(timer);

    int result = uv_timer_stop(&timer_obj->m_uv_timer);

    if (result != 0) return io_result_mk_error("failed to stop uv_timer");

    if (timer_obj->m_promise != NULL) {
        lean_dec(timer_obj->m_promise);
        timer_obj->m_promise = NULL;
    };

    return lean_io_result_mk_ok(lean_box(0));
}

#else

extern "C" lean_obj_res lean_uv_initialize() {
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_mk(obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_mk is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_run(b_obj_arg loop, uint8_t mode, obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_run is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg loop, b_obj_arg options, obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_configure is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_close(b_obj_arg loop, obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_close is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_stop(b_obj_arg loop, obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_stop is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(b_obj_arg loop, obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_alive is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_now(b_obj_arg loop, obj_arg /* w */) {
    lean_internal_panic("lean_uv_event_loop_now is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(b_obj_arg loop, uint64_t timeout, obj_arg /* w */) {
    lean_internal_panic("lean_uv_timer_mk is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */) {
    lean_internal_panic("lean_uv_timer_next is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */) {
    lean_internal_panic("lean_uv_timer_stop is not supported");
}


#endif
