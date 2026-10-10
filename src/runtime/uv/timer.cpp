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
static void lean_uv_timer_finalizer(void* ptr) {
    lean_uv_timer_object * timer = (lean_uv_timer_object*) ptr;

    lean_object * promise;

    {
        // A repeating timer without a pending promise may still be running, so the handle is closed
        // under the loop lock that its callback runs under.
        event_loop_guard guard;

        // The Lean object is being freed, so the close callback gets the struct instead. No callback
        // reads `data` as the Lean object after `uv_close`.
        timer->m_uv_timer.data = timer;

        uv_close((uv_handle_t*)&timer->m_uv_timer, [](uv_handle_t* handle) {
            free(handle->data);
        });

        // The close callback may free `timer` as soon as the lock is released.
        promise = timer->m_promise;
    }

    if (promise != NULL) {
        lean_dec(promise);
    }
}

void initialize_libuv_timer() {
    g_uv_timer_external_class = lean_register_external_class(lean_uv_timer_finalizer, [](void* obj, lean_object* f) {
        lean_object* promise = ((lean_uv_timer_object*)obj)->m_promise;

        if (promise != NULL) {
            lean_inc(f);
            lean_inc(promise);
            lean_dec(lean_apply_1(f, promise));
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
        // A tick without a promise is dropped. Without one the loop holds no reference, but the timer
        // is still alive, since its finalizer closes the handle under the loop lock that this callback
        // runs under.
        if (timer->m_promise != NULL) {
            // The field's reference moves to `promise`, and the loop's reference is released with it,
            // so that a timer that nothing waits on is freed once it is dropped. `next` takes both again.
            lean_object * promise = timer->m_promise;
            timer->m_promise = NULL;
            lean_dec(obj);

            // The timer may be freed by now, so nothing below may touch it. Code holding the promise
            // may have resolved it already.
            if (!promise_is_resolved(promise)) {
                lean_object* res = lean_io_promise_resolve(lean_box(0), promise);
                lean_dec(res);
            }
            lean_dec(promise);
        }
    } else {
        uv_timer_stop(&timer->m_uv_timer);
        timer->m_state = TIMER_STATE_FINISHED;

        lean_object * promise = timer->m_promise;
        if (promise != NULL) {
            lean_inc(promise);
        }

        // The loop does not need to keep the timer alive anymore.
        lean_dec(obj);

        // The timer may be freed by now, so nothing below may touch it. Code holding the promise may
        // have resolved it already.
        if (promise != NULL) {
            if (!promise_is_resolved(promise)) {
                lean_object* res = lean_io_promise_resolve(lean_box(0), promise);
                lean_dec(res);
            }
            lean_dec(promise);
        }
    }
}

/* Std.Internal.UV.Timer.mk (timeout : UInt64) (repeating : Bool) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating) {
    lean_uv_timer_object * timer = (lean_uv_timer_object*)malloc(sizeof(lean_uv_timer_object));
    if (timer == nullptr) {
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }
    // libuv treats a repeat period of 0 as a one-shot timer.
    timer->m_timeout = repeating && timeout == 0 ? 1 : timeout;
    timer->m_repeating = repeating;
    timer->m_state = TIMER_STATE_INITIAL;
    timer->m_promise = NULL;

    int result;

    {
        event_loop_guard guard;
        result = uv_timer_init(global_ev.m_loop, &timer->m_uv_timer);
    }

    if (result != 0) {
        free(timer);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    lean_object * obj = lean_uv_timer_new(timer);
    lean_mark_mt(obj);
    timer->m_uv_timer.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    auto create_promise = []() {
        lean_object * promise = lean_io_promise_new();
        // The loop thread resolves and releases it, so its refcount has to be atomic.
        mark_mt(promise);
        return promise;
    };

    // Stays NULL when `stop` dropped this timer's promise.
    lean_object * promise = NULL;
    int result = 0;

    auto setup_timer = [&]() {
        lean_assert(timer->m_promise == NULL);

        promise = create_promise();
        timer->m_promise = promise;
        timer->m_state = TIMER_STATE_RUNNING;

        // The event loop must keep the timer alive for the duration of the run time.
        lean_inc(obj);
        lean_inc(promise);

        result = uv_timer_start(
            &timer->m_uv_timer,
            handle_timer_event,
            timer->m_repeating ? 0 : timer->m_timeout,
            timer->m_repeating ? timer->m_timeout : 0
        );

        if (result != 0) {
            // A failed start must not leave the timer advertising a promise the loop will settle.
            timer->m_state = TIMER_STATE_INITIAL;
            timer->m_promise = NULL;
        }
    };

    {
        event_loop_guard guard;

        if (timer->m_repeating) {
            switch (timer->m_state) {
                case TIMER_STATE_INITIAL:
                    setup_timer();
                    break;
                case TIMER_STATE_RUNNING:
                    if (timer->m_promise == NULL || timer_promise_is_finished(timer)) {
                        if (timer->m_promise != NULL) {
                            lean_dec(timer->m_promise);
                        } else {
                            // A tick or `cancel` released the loop's reference along with the promise.
                            lean_inc(obj);
                        }

                        timer->m_promise = create_promise();
                    }

                    promise = timer->m_promise;
                    lean_inc(promise);
                    break;
                case TIMER_STATE_FINISHED:
                    if (timer->m_promise != NULL) {
                        promise = timer->m_promise;
                        lean_inc(promise);
                    }
                    break;
            }
        } else if (timer->m_state == TIMER_STATE_INITIAL) {
            setup_timer();
        } else if (timer->m_promise != NULL) {
            promise = timer->m_promise;
            lean_inc(promise);
        }
    }

    if (result != 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(obj);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    if (promise == NULL) {
        // `stop` dropped this timer's promise, so the fresh one is never resolved, as documented on
        // `next`.
        promise = create_promise();
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.Timer.reset (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    int result = 0;

    {
        // Locking to access the state in order to avoid data-race
        event_loop_guard guard;

        if (timer->m_state == TIMER_STATE_RUNNING) {
            uv_timer_stop(&timer->m_uv_timer);

            result = uv_timer_start(
                &timer->m_uv_timer,
                handle_timer_event,
                timer->m_timeout,
                timer->m_repeating ? timer->m_timeout : 0
            );
        }
    }

    if (result != 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.stop (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    lean_object * promise = NULL;

    {
        event_loop_guard guard;

        if (timer->m_state == TIMER_STATE_RUNNING) {
            uv_timer_stop(&timer->m_uv_timer);
            promise = timer->m_promise;
            timer->m_promise = NULL;
            timer->m_state = TIMER_STATE_FINISHED;
        }
    }

    // Released after the state change and outside the lock, since dropping the last reference
    // runs continuations inline, which may re-enter this handle.
    if (promise != NULL) {
        lean_dec(promise);
        // The loop holds a reference only while a promise is pending.
        lean_dec(obj);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.cancel (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_cancel(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    lean_object * promise = NULL;

    {
        // It's locking here to avoid changing the state during other operations.
        event_loop_guard guard;

        if (timer->m_state == TIMER_STATE_RUNNING && timer->m_promise != NULL) {
            promise = timer->m_promise;
            timer->m_promise = NULL;

            // A repeating timer keeps running, but the loop stops keeping it alive, so a timer that is
            // dropped instead is closed by its finalizer.
            if (!timer->m_repeating) {
                uv_timer_stop(&timer->m_uv_timer);
                timer->m_state = TIMER_STATE_INITIAL;
            }
        }
    }

    // Released after the state change and outside the lock, since dropping the last reference
    // runs continuations inline, which may re-enter this handle.
    if (promise != NULL) {
        lean_dec(promise);
        // The loop holds a reference only while a promise is pending.
        lean_dec(obj);
    }

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
