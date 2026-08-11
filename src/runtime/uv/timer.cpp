/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/timer.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

void lean_uv_timer_finalizer(void* ptr) {
    lean_uv_timer_object* timer = (lean_uv_timer_object*) ptr;

    // `m_promise` must only be released once the loop state is known: if the loop is gone,
    // `lean_uv_timer_shutdown` has already released it during the teardown walk.
    if (!event_loop_lock(&global_ev)) {
        event_loop_wait_finalized(&global_ev);
        if (timer->m_uv_timer != nullptr) {
            free(timer->m_uv_timer);
        }
        free(timer);
        return;
    }

    if (timer->m_promise != NULL) {
        lean_dec(timer->m_promise);
    }

    uv_close((uv_handle_t*) timer->m_uv_timer, [](uv_handle_t* handle) {
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
    return promise_is_resolved(timer->m_promise);
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
            lean_object* res = lean_io_promise_resolve(mk_except_ok(lean_box(0)), timer->m_promise);
            lean_dec(res);
        }
    } else {
        // For non-repeating timers, resolves if the promise exists
        if (timer->m_promise != NULL) {
            lean_assert(!timer_promise_is_finished(timer));
            lean_object* res = lean_io_promise_resolve(mk_except_ok(lean_box(0)), timer->m_promise);
            lean_dec(res);
        }

        uv_timer_stop(timer->m_uv_timer);
        timer->m_state = TIMER_STATE_FINISHED;

        // The loop does not need to keep the timer alive anymore.
        lean_dec(obj);
    }
}

size_t lean_uv_timer_shutdown(lean_uv_timer_object * timer) {
    size_t release_refs = 0;

    if (timer->m_state == TIMER_STATE_RUNNING) {
        // `cancel` on a repeating timer leaves it running without a promise, in which case the loop
        // has already given its reference back.
        if (timer->m_promise != NULL) {
            release_refs += 1;
        }

        uv_timer_stop(timer->m_uv_timer);
        timer->m_state = TIMER_STATE_FINISHED;
    }

    if (timer->m_promise != NULL) {
        if (!timer_promise_is_finished(timer)) {
            lean_promise_resolve_with_code(UV_ECANCELED, timer->m_promise);
        }

        lean_dec(timer->m_promise);
        timer->m_promise = NULL;
    }

    timer->m_uv_timer = nullptr;
    return release_refs;
}

/* Std.Internal.UV.Timer.mk (timeout : UInt64) (repeating : Bool) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating) {
    lean_uv_timer_object * timer = (lean_uv_timer_object*)malloc(sizeof(lean_uv_timer_object));
    if (timer == nullptr) {
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }
    uv_timer_t * uv_timer = (uv_timer_t*)malloc(sizeof(uv_timer_t));
    if (uv_timer == nullptr) {
        free(timer);
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }

    timer->m_uv_timer = uv_timer;
    timer->m_timeout = timeout;
    timer->m_repeating = repeating;
    timer->m_state = TIMER_STATE_INITIAL;
    timer->m_promise = NULL;

    if (!event_loop_lock(&global_ev)) {
        free(uv_timer);
        free(timer);
        return lean_uv_loop_unavailable_error();
    }
    int result = uv_timer_init(global_ev.loop, uv_timer);

    if (result != 0) {
        event_loop_unlock(&global_ev);
        free(uv_timer);
        free(timer);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    lean_object * obj = lean_uv_timer_new(timer);
    lean_mark_mt(obj);
    timer->m_uv_timer->data = obj;

    event_loop_unlock(&global_ev);

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
            // Restore the pre-call state: leaving `RUNNING` behind would make the teardown walk
            // believe the loop still holds the reference released just below.
            timer->m_state = TIMER_STATE_INITIAL;
            timer->m_promise = NULL;

            lean_dec(promise); // The structure does not own it.
            lean_dec(promise); // We are not going to return it.
            lean_dec(obj);

            event_loop_unlock(&global_ev);
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        }

        event_loop_unlock(&global_ev);

        return lean_io_result_mk_ok(promise);
    };

    if (!event_loop_lock(&global_ev)) {
        return lean_uv_loop_unavailable_error();
    }

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
                        } else {
                            // Re-arming after `cancel`: the loop owes a promise again, so it takes
                            // its reference on the timer back.
                            lean_inc(obj);
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
    if (!event_loop_lock(&global_ev)) {
        return lean_uv_loop_unavailable_error();
    }

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

    if (!event_loop_lock(&global_ev)) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    // `cancel` on a repeating timer leaves it running without a promise, in which case the loop has
    // already given its reference back and must not be charged for it twice.
    bool loop_owns_timer = timer->m_state == TIMER_STATE_RUNNING && timer->m_promise != NULL;

    if (timer->m_promise != NULL) {
        lean_dec(timer->m_promise);
        timer->m_promise = NULL;
    }

    if (timer->m_state == TIMER_STATE_RUNNING) {
        uv_timer_stop(timer->m_uv_timer);
        timer->m_state = TIMER_STATE_FINISHED;

        event_loop_unlock(&global_ev);

        if (loop_owns_timer) {
            // The loop does not need to keep the timer alive anymore.
            lean_dec(obj);
        }

        return lean_io_result_mk_ok(lean_box(0));
    }

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.cancel (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_cancel(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // It's locking here to avoid changing the state during other operations.
    if (!event_loop_lock(&global_ev)) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    if (timer->m_state == TIMER_STATE_RUNNING && timer->m_promise != NULL) {
        if (timer->m_repeating) {
            lean_dec(timer->m_promise);
            timer->m_promise = NULL;

            // The timer keeps ticking, but it no longer owes anyone a promise, so the loop gives
            // its reference back. Otherwise a dropped repeating timer could never be reclaimed:
            // the reference kept it alive and only it could have released the reference.
            lean_dec(obj);
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
