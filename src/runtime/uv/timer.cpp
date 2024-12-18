/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#include "runtime/uv/timer.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

// The finalizer of the `Timer`.
// TODO: check if it can cause the promise to leak in some way.
void lean_uv_timer_finalizer(void* ptr) {
    lean_uv_timer_object * timer_obj = (lean_uv_timer_object*) ptr;
    timer_obj->m_uv_timer.data = ptr;

    if (timer_obj->m_promise != NULL) {
        lean_dec(timer_obj->m_promise);
    }

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*) & timer_obj->m_uv_timer, [](uv_handle_t* handle) {
        free((lean_uv_timer_object*)handle->data);
    });

    event_loop_unlock(&global_ev);
}

void initialize_libuv_timer() {
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, [](void* obj, lean_object* f) {
        lean_inc(f);

        if (((lean_uv_timer_object*)obj)->m_promise != NULL) {
            lean_apply_1(f, ((lean_uv_timer_object*)obj)->m_promise);
        }
    });
}

void handle_timer_event(uv_timer_t* handle) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    if (!timer->m_repeating) {
        uv_timer_stop(&timer->m_uv_timer);
    }

    if (timer->m_promise != NULL) {
        if (lean_io_get_task_state_core(timer->m_promise) == 2) return;

        lean_object* res = lean_io_promise_resolve(lean_box(0), timer->m_promise, lean_io_mk_world());
        lean_dec(res);

        /// The loop does not owns the object anymore.
        lean_dec(timer->m_promise);
        lean_dec(obj);
    }
}

/* Std.Internal.UV.Timer.mk (timeout : UInt64) (repeating : Bool) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating, obj_arg /* w */) {
    lean_uv_timer_object * timer_obj = (lean_uv_timer_object*)malloc(sizeof(lean_uv_timer_object));
    timer_obj->m_timeout = timeout;
    timer_obj->m_repeating = repeating;
    timer_obj->m_started = false;
    timer_obj->m_promise = NULL;

    event_loop_lock(&global_ev);
    int result = uv_timer_init(global_ev.loop, &timer_obj->m_uv_timer);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(timer_obj);
        return io_result_mk_error("failed to initialize uv_timer");
    }

    lean_object * obj = lean_uv_timer_new(timer_obj);
    timer_obj->m_uv_timer.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */ ) {
    lean_uv_timer_object * obj = lean_to_uv_timer(timer);

    bool is_unresolved = obj->m_promise != NULL && lean_io_get_task_state_core(obj->m_promise) != 2;

    auto create_promise = []() {
        lean_object * prom_res = lean_io_promise_new(lean_io_mk_world());
        lean_object * promise = lean_ctor_get(prom_res, 0);
        lean_inc(promise);
        lean_dec(prom_res);

        return promise;
    };

    if (!obj->m_started) {
        if (obj->m_promise != NULL) lean_dec(obj->m_promise);
        lean_object * promise = create_promise();

        obj->m_promise = promise;
        obj->m_started = true;

        // The object owns the promise
        lean_inc(promise);

        // The event loop owns the timer again.
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
            lean_object * promise = create_promise();

            if (obj->m_promise != NULL) lean_dec(obj->m_promise);
            obj->m_promise = promise;

            // The object owns the promise
            lean_inc(promise);

            // The event loop owns the promise and the
            // object.
            lean_inc(promise);
            lean_inc(timer);

            return lean_io_result_mk_ok(promise);
        }
    }
}

/* Std.Internal.UV.Timer.reset (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer, obj_arg /* w */ ) {
    lean_uv_timer_object * obj = lean_to_uv_timer(timer);

    if (!obj->m_started ||(obj->m_promise != NULL && lean_io_get_task_state_core(obj->m_promise) == 2)) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    event_loop_lock(&global_ev);

    uv_timer_stop(&obj->m_uv_timer);

    uv_timer_start(
        &obj->m_uv_timer,
        handle_timer_event,
        obj->m_timeout,
        obj->m_repeating ? obj->m_timeout : 0
    );

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.stop (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */) {
    lean_uv_timer_object * obj = lean_to_uv_timer(timer);

    if (!obj->m_started) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    event_loop_lock(&global_ev);
    uv_timer_stop(&obj->m_uv_timer);
    event_loop_unlock(&global_ev);

    obj->m_started = false;

    // If the promise is in progress it means that it's owned by the event loop, so we need
    // remove the ownership by reducing the reference count of the object.
    if (obj->m_promise != NULL && lean_io_get_task_state_core(obj->m_promise) != 2) {
        lean_dec(obj->m_promise);
        lean_dec(timer);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

#else

void lean_uv_timer_finalizer(void* ptr);

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating, obj_arg /* w */) {
    return io_result_mk_error("lean_uv_timer_mk is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */ ) {
    return io_result_mk_error("lean_uv_timer_next is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer, obj_arg /* w */ ) {
    return io_result_mk_error("lean_uv_timer_reset is not supported");
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */ ) {
    return io_result_mk_error("lean_uv_timer_stop is not supported");
}

#endif
}