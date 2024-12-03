/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include <pthread.h>

#include "runtime/event_loop.h"
#include "runtime/libuv.h"
#include "runtime/object.h"

namespace lean {

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

// The multithreaded event loop object for all tasks in the task manager.
event_loop_t global_ev;

// The finalizer of the `Timer`.
// TODO: check if it can cause the promise to leak in some way.
static void lean_uv_timer_finalizer(void* ptr) {
    lean_uv_timer_object* timer_obj = (lean_uv_timer_object*) ptr;
    timer_obj->m_uv_timer.data = ptr;

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*) & timer_obj->m_uv_timer, [](uv_handle_t* handle) {
        free((lean_uv_timer_object*)handle->data);
    });

    event_loop_unlock(&global_ev);

    if (timer_obj->m_promise != NULL) lean_dec(timer_obj->m_promise);
}

// Registers the foreign classes and starts the event loop.
extern "C" void initialize_libuv() {
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, noop_foreach);
    event_loop_init(&global_ev);

    lthread([]() { event_loop_run_loop(&global_ev); });
}

/* Lean.libUVVersionFn : Unit → Nat */
extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ ) {
    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    event_loop_lock(&global_ev);

    if (accum && uv_loop_configure(global_ev.loop, UV_METRICS_IDLE_TIME) != 0) {
        return io_result_mk_error("failed to configure global_ev.loop with UV_METRICS_IDLE_TIME");
    }

    #if!defined(WIN32) && !defined(_WIN32)
    if (block && uv_loop_configure(global_ev.loop, UV_LOOP_BLOCK_SIGNAL, SIGPROF) != 0) {
        return io_result_mk_error("failed to configure global_ev.loop with UV_LOOP_BLOCK_SIGNAL");
    }
    #endif

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Loop.alive : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ ) {
    event_loop_lock(&global_ev);
    int is_alive = uv_loop_alive(global_ev.loop);
    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(lean_box(is_alive));
}

void handle_timer_event(uv_timer_t* handle) {
    lean_object* obj = (lean_object*)handle->data;
    lean_uv_timer_object* timer = lean_to_uv_timer(obj);

    // If the last promise is already solved then we can just set it as closed.
    // and free the object.
    if(!timer->m_repeating || (timer->m_promise != NULL && lean_io_get_task_state_core(timer->m_promise) == 2)) {
        timer->m_started = false;
    }

    if (timer->m_promise != NULL) {
        lean_io_promise_resolve(lean_box(0), timer->m_promise, lean_io_mk_world());
    }

    if (!timer->m_started || !timer->m_repeating) {
        uv_timer_stop(&timer->m_uv_timer);

        // The event loop losts ownership over them.
        lean_dec(timer->m_promise);
        lean_dec(obj);

        timer->m_promise = NULL;
    }
}

/* Std.Internal.UV.Timer.mk (timeout : UInt64) (repeating : Bool) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating, obj_arg /* w */ ) {
    lean_uv_timer_object* timer_obj = (lean_uv_timer_object*)malloc(sizeof(lean_uv_timer_object));

    timer_obj->m_timeout = timeout;
    timer_obj->m_repeating = repeating;
    timer_obj->m_started = false;
    timer_obj->m_promise = NULL;

    lean_object* obj = lean_uv_timer_new(timer_obj);

    event_loop_lock(&global_ev);
    int result = uv_timer_init(global_ev.loop, &timer_obj->m_uv_timer);
    timer_obj->m_uv_timer.data = obj;
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(timer_obj);
        return io_result_mk_error("failed to initialize uv_timer");
    }

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */ ) {
    lean_uv_timer_object* obj = lean_to_uv_timer(timer);

    bool is_unresolved = obj->m_promise != NULL && lean_io_get_task_state_core(obj->m_promise) != 2;

    auto create_promise = []() {
        lean_object* prom_res = lean_io_promise_new(lean_io_mk_world());
        lean_object* promise = lean_ctor_get(prom_res, 0);
        lean_inc(promise);
        lean_dec(prom_res);
        return promise;
    };

    if (!obj->m_started) {
        if (obj->m_promise != NULL) lean_dec(obj->m_promise);
        lean_object* promise = create_promise();

        obj->m_promise = promise;
        obj->m_started = true;

        lean_inc(promise);
        lean_inc(timer);

        event_loop_lock(&global_ev);

        int result = uv_timer_start(
            &obj->m_uv_timer,
            handle_timer_event,
            obj->m_repeating ? 0 : obj->m_timeout,
            obj->m_repeating ? obj->m_timeout : 0
        );

        event_loop_unlock(&global_ev);

        if (result != 0) return io_result_mk_error("failed to start uv_timer");
        return lean_io_result_mk_ok(promise);
    } else {
        if (is_unresolved || !obj->m_repeating) {
            lean_inc(obj->m_promise);
            return lean_io_result_mk_ok(obj->m_promise);
        } else {
            lean_object* promise = create_promise();
            if (obj->m_promise != NULL) lean_dec(obj->m_promise);
            obj->m_promise = promise;

            lean_inc(promise);

            return lean_io_result_mk_ok(promise);
        }
    }
}

/* Std.Internal.UV.Timer.reset (timer : Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer, obj_arg /* w */ ) {
    lean_uv_timer_object* obj = lean_to_uv_timer(timer);

    if (!obj->m_started) return lean_io_result_mk_ok(lean_box(0));
    obj->m_started = false;

    return lean_io_result_mk_ok(lean_box(0));
}

#else

extern "C" void initialize_libuv() {}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_event_loop_configure is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_event_loop_alive is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_timer_mk is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_timer_next is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer, obj_arg /* w */ ) {
    lean_internal_panic("lean_uv_timer_reset is not supported");
}

#endif
}