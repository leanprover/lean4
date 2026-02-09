/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/timer.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

// The finalizer of the `Timer`.
void lean_uv_timer_finalizer(void* ptr) {
    lean_uv_timer_object * timer = (lean_uv_timer_object*) ptr;

    /// The timer can be null in two states, it has not started and it got cancelled.
    if (timer->m_promise != NULL) {
        lean_dec(timer->m_promise);
    }

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*)timer->m_uv_timer, [](uv_handle_t* handle) {
        free(handle);
    });

    event_loop_unlock(&global_ev);

    free(timer);
}

void initialize_libuv_timer() {
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, [](void* obj, lean_object* f) {
        if (((lean_uv_timer_object*)obj)->m_promise != NULL) {
            lean_inc(f);
            lean_apply_1(f, ((lean_uv_timer_object*)obj)->m_promise);
        }
    });
}

static bool timer_promise_is_finished(lean_uv_timer_object * timer) {
    return lean_io_get_task_state_core((lean_object *)lean_to_promise(timer->m_promise)->m_result) == 2;
}

void handle_timer_event(uv_timer_t* handle) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // handle_timer_event may only be called while the timer is running. The promise can be NULL
    // if the last promise was cancelled.
    lean_assert(timer->m_state == TIMER_STATE_RUNNING);

   if (timer->m_repeating) {
        // For repeating timers, only resolves if the promise exists and is not finished
        if (timer->m_promise != NULL && !timer_promise_is_finished(timer)) {
            lean_object* res = lean_io_promise_resolve(lean_box(0), timer->m_promise);
            lean_dec(res);
        }
    } else {
        // For non-repeating timers, resolves if the promise exists
        if (timer->m_promise != NULL) {
            lean_assert(!timer_promise_is_finished(timer));
            lean_object* res = lean_io_promise_resolve(lean_box(0), timer->m_promise);
            lean_dec(res);
        }

        uv_timer_stop(timer->m_uv_timer);
        timer->m_state = TIMER_STATE_FINISHED;

        // The loop does not need to keep the timer alive anymore.
        lean_dec(obj);
    }
}

/* Std.Internal.UV.Timer.mk (timeout : UInt64) (repeating : Bool) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating) {
    lean_uv_timer_object * timer = (lean_uv_timer_object*)malloc(sizeof(lean_uv_timer_object));
    timer->m_timeout = timeout;
    timer->m_repeating = repeating;
    timer->m_state = TIMER_STATE_INITIAL;
    timer->m_promise = NULL;

    uv_timer_t * uv_timer = (uv_timer_t*)malloc(sizeof(uv_timer_t));

    event_loop_lock(&global_ev);
    int result = uv_timer_init(global_ev.loop, uv_timer);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(uv_timer);
        free(timer);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    timer->m_uv_timer = uv_timer;

    lean_object * obj = lean_uv_timer_new(timer);
    lean_mark_mt(obj);
    timer->m_uv_timer->data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    auto create_promise = []() {
        return lean_io_promise_new();
    };

    auto setup_timer = [create_promise, obj, timer]() {
        lean_assert(timer->m_promise == NULL);

        lean_object* promise = create_promise();
        timer->m_promise = promise;
        timer->m_state = TIMER_STATE_RUNNING;

        // The event loop must keep the timer alive for the duration of the run time.
        lean_inc(obj);
        lean_inc(promise);

        int result = uv_timer_start(
            timer->m_uv_timer,
            handle_timer_event,
            timer->m_repeating ? 0 : timer->m_timeout,
            timer->m_repeating ? timer->m_timeout : 0
        );

        if (result != 0) {
            lean_dec(obj);
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        }

        event_loop_unlock(&global_ev);

        return lean_io_result_mk_ok(promise);
    };

    event_loop_lock(&global_ev);

    if (timer->m_repeating) {
        switch (timer->m_state) {
            case TIMER_STATE_INITIAL:
                {
                    return setup_timer();
                }
            case TIMER_STATE_RUNNING:
                {
                    if (timer->m_promise == NULL || timer_promise_is_finished(timer)) {
                        if (timer->m_promise != NULL) {
                            lean_dec(timer->m_promise);
                        }

                        timer->m_promise = create_promise();
                    }

                    lean_inc(timer->m_promise);

                    event_loop_unlock(&global_ev);

                    return lean_io_result_mk_ok(timer->m_promise);
                }
            case TIMER_STATE_FINISHED:
                {
                    if (timer->m_promise != NULL) {
                        lean_inc(timer->m_promise);
                        event_loop_unlock(&global_ev);
                        return lean_io_result_mk_ok(timer->m_promise);
                    } else {
                        // Creates a resolved promise
                        lean_object* finished_promise = create_promise();
                        event_loop_unlock(&global_ev);
                        return lean_io_result_mk_ok(finished_promise);
                    }
                }
        }
    } else {
        if (timer->m_state == TIMER_STATE_INITIAL) {
            return setup_timer();
        } else if (timer->m_promise != NULL) {
            lean_inc(timer->m_promise);
            lean_object* promise = timer->m_promise;
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(promise);
        } else {
            event_loop_unlock(&global_ev);
            // Creates a resolved promise
            lean_object* finished_promise = create_promise();
            return lean_io_result_mk_ok(finished_promise);
        }
    }
}

/* Std.Internal.UV.Timer.reset (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // Locking to access the state in order to avoid data-race
    event_loop_lock(&global_ev);

    if (timer->m_state == TIMER_STATE_RUNNING) {

        uv_timer_stop(timer->m_uv_timer);

        int result = uv_timer_start(
            timer->m_uv_timer,
            handle_timer_event,
            timer->m_timeout,
            timer->m_repeating ? timer->m_timeout : 0
        );

        event_loop_unlock(&global_ev);

        if (result != 0) {
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        } else {
            return lean_io_result_mk_ok(lean_box(0));
        }
    } else {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(lean_box(0));
    }
}

/* Std.Internal.UV.Timer.stop (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // Locking to access the state in order to avoid data-race
    event_loop_lock(&global_ev);

    if (timer->m_promise != NULL) {
        lean_dec(timer->m_promise);
        timer->m_promise = NULL;
    }

    if (timer->m_state == TIMER_STATE_RUNNING) {
        uv_timer_stop(timer->m_uv_timer);
        event_loop_unlock(&global_ev);

        timer->m_state = TIMER_STATE_FINISHED;

        // The loop does not need to keep the timer alive anymore.
        lean_dec(obj);

        return lean_io_result_mk_ok(lean_box(0));
    }

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.cancel (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_cancel(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // It's locking here to avoid changing the state during other operations.
    event_loop_lock(&global_ev);

    if (timer->m_state == TIMER_STATE_RUNNING && timer->m_promise != NULL) {
        if (timer->m_repeating) {
            lean_dec(timer->m_promise);
            timer->m_promise = NULL;
        } else {
            uv_timer_stop(timer->m_uv_timer);

            lean_dec(timer->m_promise);
            timer->m_promise = NULL;
            timer->m_state = TIMER_STATE_INITIAL;

            // The loop does not need to keep the timer alive anymore.
            lean_dec(obj);
        }
    }

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(lean_box(0));
}

#else

void lean_uv_timer_finalizer(void* ptr);

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_cancel(b_obj_arg obj) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
