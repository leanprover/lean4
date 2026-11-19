/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/timer.h"
#include "runtime/uv/util.h"
#include <new>

namespace lean {
#ifndef LEAN_EMSCRIPTEN

// The finalizer of the `Timer`.
static void timer_finalizer(void* ptr) {
    lean_uv_timer_object * timer = (lean_uv_timer_object*) ptr;

    // Released after the unlock.
    owned_ref promise;

    {
        // A repeating timer without a pending promise may still be running, so the handle is closed
        // under the loop lock that its callback runs under.
        event_loop_guard guard;

        // The close callback may free `timer` as soon as the lock is released.
        promise = std::move(timer->m_promise);
        // While a promise is pending the loop holds a reference, so the timer cannot be finalized.
        lean_assert(promise.get() == nullptr || promise_is_resolved(promise.get()));

        // The teardown at exit already closed the handle.
        if (uv_is_closing((uv_handle_t*)&timer->m_uv_timer)) {
            delete timer;
            return;
        }

        // The Lean object is being freed, so the close callback gets the struct instead. No callback
        // reads `data` as the Lean object after `uv_close`.
        timer->m_uv_timer.data = timer;

        uv_close((uv_handle_t*)&timer->m_uv_timer, [](uv_handle_t* handle) {
            delete static_cast<lean_uv_timer_object*>(handle->data);
        });
    }
}

void initialize_libuv_timer() {
    g_uv_timer_external_class = lean_register_external_class(timer_finalizer, uv_foreach_refs<lean_uv_timer_object>);
}

static void handle_timer_event(uv_timer_t* handle) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // handle_timer_event may only be called while the timer is running. The promise can be null
    // if the last promise was cancelled.
    lean_assert(timer->m_state == timer_state::Running);

    owned_ref promise;

    if (timer->m_repeating) {
        // A tick without a promise is dropped. Without one the loop holds no reference, but the timer
        // is still alive, since its finalizer closes the handle under the loop lock that this callback
        // runs under.
        if (timer->m_promise.get() == nullptr) {
            return;
        }

        // The field's reference moves to `promise`, and the loop's reference is released with it,
        // so that a timer that nothing waits on is freed once it is dropped. `next` takes both again.
        promise = std::move(timer->m_promise);
    } else {
        uv_timer_stop(&timer->m_uv_timer);
        timer->m_state = timer_state::Finished;

        // The timer keeps its promise, so that a later `next` returns it.
        if (timer->m_promise.get() != nullptr) {
            promise = owned_ref::retain(timer->m_promise.get());
        }
    }

    // Code holding the promise may have resolved it already.
    if (promise.get() != nullptr && !promise_is_resolved(promise.get())) {
        lean_dec(lean_io_promise_resolve(lean_box(0), promise.get()));
    }

    // Released only after resolving: when the loop holds the last reference, as for a dropped
    // `Sleep`, this runs the finalizer, which must not drop a pending promise. A one-shot timer is
    // already finished, so continuations run by the resolve cannot have released this reference.
    lean_dec(obj);
}

/* Std.Internal.UV.Timer.mk (timeout : UInt64) (repeating : Bool) : IO Timer */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating) {
    lean_uv_timer_object * timer = new (std::nothrow) lean_uv_timer_object;
    if (timer == nullptr) {
        return io_result_mk_enomem();
    }
    // libuv treats a repeat period of 0 as a one-shot timer.
    timer->m_timeout = repeating && timeout == 0 ? 1 : timeout;
    timer->m_repeating = repeating;

    int result;

    {
        event_loop_guard guard;

        if (guard.stopped()) {
            delete timer;
            return io_result_mk_uv_error(UV_ECANCELED);
        }

        result = uv_timer_init(global_ev.m_loop, &timer->m_uv_timer);
    }

    if (result != 0) {
        delete timer;
        return io_result_mk_uv_error(result);
    }

    lean_object * obj = lean_uv_timer_new(timer);
    lean_mark_mt(obj);
    timer->m_uv_timer.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Timer.next (timer : @& Timer) : IO (IO.Promise Unit) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    owned_ref promise;
    // A promise the timer lets go of: a settled one being replaced, or the one of a failed start.
    owned_ref dropped;
    int result = 0;

    {
        event_loop_guard guard;

        if (guard.closed(&timer->m_uv_timer)) {
            return io_result_mk_uv_error(UV_ECANCELED);
        }

        if (timer->m_state == timer_state::Initial) {
            timer->m_promise = owned_ref(mk_mt_promise());

            result = uv_timer_start(
                &timer->m_uv_timer,
                handle_timer_event,
                timer->m_repeating ? 0 : timer->m_timeout,
                timer->m_repeating ? timer->m_timeout : 0
            );

            if (result == 0) {
                timer->m_state = timer_state::Running;
                // The event loop keeps the timer alive while a promise is pending.
                lean_inc(obj);
            } else {
                // A failed start must not leave the timer advertising a promise the loop will settle.
                dropped = std::move(timer->m_promise);
            }
        } else if (timer->m_repeating && timer->m_state == timer_state::Running &&
                   (timer->m_promise.get() == nullptr || promise_is_resolved(timer->m_promise.get()))) {
            if (timer->m_promise.get() == nullptr) {
                // A tick or `cancel` released the loop's reference along with the promise.
                lean_inc(obj);
            }

            dropped = std::move(timer->m_promise);
            timer->m_promise = owned_ref(mk_mt_promise());
        }

        if (timer->m_promise.get() != nullptr) {
            promise = owned_ref::retain(timer->m_promise.get());
        }
    }

    if (result != 0) {
        return io_result_mk_uv_error(result);
    }

    // Without a promise, `stop` dropped this timer's promise, so the fresh one is never resolved, as
    // documented on `next`.
    return lean_io_result_mk_ok(promise.get() != nullptr ? promise.release() : mk_mt_promise());
}

/* Std.Internal.UV.Timer.reset (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    int result = 0;

    {
        // Locking to access the state in order to avoid data-race
        event_loop_guard guard;

        if (guard.closed(&timer->m_uv_timer)) {
            return io_result_mk_uv_error(UV_ECANCELED);
        }

        if (timer->m_state == timer_state::Running) {
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
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.stop (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // Released after the state change and outside the lock, since dropping the last reference runs
    // continuations inline, which may re-enter this handle.
    owned_ref promise;

    {
        event_loop_guard guard;

        if (guard.closed(&timer->m_uv_timer)) {
            return io_result_mk_uv_error(UV_ECANCELED);
        }

        if (timer->m_state == timer_state::Running) {
            uv_timer_stop(&timer->m_uv_timer);
            promise = std::move(timer->m_promise);
            timer->m_state = timer_state::Finished;
        }
    }

    // The loop holds a reference only while a promise is pending.
    if (promise.get() != nullptr) {
        lean_dec(obj);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Timer.cancel (timer : @& Timer) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_cancel(b_obj_arg obj) {
    lean_uv_timer_object * timer = lean_to_uv_timer(obj);

    // Released after the state change and outside the lock, since dropping the last reference runs
    // continuations inline, which may re-enter this handle.
    owned_ref promise;

    {
        // It's locking here to avoid changing the state during other operations.
        event_loop_guard guard;

        if (guard.closed(&timer->m_uv_timer)) {
            return io_result_mk_uv_error(UV_ECANCELED);
        }

        if (timer->m_state == timer_state::Running && timer->m_promise.get() != nullptr) {
            promise = std::move(timer->m_promise);

            // A repeating timer keeps running, but the loop stops keeping it alive, so a timer that is
            // dropped instead is closed by its finalizer.
            if (!timer->m_repeating) {
                uv_timer_stop(&timer->m_uv_timer);
                timer->m_state = timer_state::Initial;
            }
        }
    }

    // The loop holds a reference only while a promise is pending.
    if (promise.get() != nullptr) {
        lean_dec(obj);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

#else

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
