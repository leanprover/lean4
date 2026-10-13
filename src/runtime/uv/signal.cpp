/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/uv/signal.h"
#include "runtime/uv/util.h"
#include <memory>
#include <new>

namespace lean {
#ifndef LEAN_EMSCRIPTEN

// The finalizer of the `Signal`.
static void signal_finalizer(void* ptr) {
    lean_uv_signal_object * signal = (lean_uv_signal_object*) ptr;

    // Released after the unlock.
    owned_ref promise;
    // Freed after the unlock when the teardown at exit already closed the handle.
    std::unique_ptr<lean_uv_signal_object> closed_at_exit;

    {
        event_loop_guard guard;

        // The close callback may free `signal` as soon as the lock is released.
        promise = std::move(signal->m_promise);
        // While a promise is pending the loop holds a reference, so the signal cannot be finalized.
        lean_assert(promise.get() == nullptr || promise_is_resolved(promise.get()));

        if (uv_is_closing((uv_handle_t*)&signal->m_uv_signal)) {
            closed_at_exit.reset(signal);
            return;
        }

        // The Lean object is being freed, so the close callback gets the struct instead. No callback
        // reads `data` as the Lean object after `uv_close`.
        signal->m_uv_signal.data = signal;

        uv_close((uv_handle_t*)&signal->m_uv_signal, [](uv_handle_t* handle) {
            delete static_cast<lean_uv_signal_object*>(handle->data);
        });
    }
}

void initialize_libuv_signal() {
    g_uv_signal_external_class = lean_register_external_class(signal_finalizer, uv_foreach_refs<lean_uv_signal_object>);
}

static bool signal_promise_is_finished(lean_uv_signal_object * signal) {
    return signal->m_promise.get() == nullptr || promise_is_resolved(signal->m_promise.get());
}

static void handle_signal_event(uv_signal_t* handle, int) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);
    int const signum = signal->m_lean_signum;

    lean_assert(signal->m_state == signal_state::Running);

    owned_ref promise;
    bool release_loop_ref = false;

    if (signal->m_repeating) {
        if (signal_promise_is_finished(signal)) {
            // Kept for the next `next`, so that a signal between two waits is not lost.
            signal->m_received = true;

            if (signal->m_promise.get() != nullptr) {
                // Its holder resolved it, so nothing waits on the signal any more. Released last, since
                // the signal may be freed with the loop's reference.
                owned_ref resolved = std::move(signal->m_promise);
                lean_dec(obj);
            }
            return;
        }

        // The field's reference moves to `promise`, and the loop's reference is released with it, so
        // that a signal that nothing waits on is freed once it is dropped. `next` takes both again.
        promise = std::move(signal->m_promise);
        lean_dec(obj);
    } else {
        uv_signal_stop(&signal->m_uv_signal);
        signal->m_state = signal_state::Finished;

        // Without a pending promise the loop holds no reference. The signal is still alive, since
        // its finalizer closes the handle under the loop lock that this callback runs under.
        release_loop_ref = signal->m_promise.get() != nullptr;
        if (!release_loop_ref) {
            // Kept for the next `next`, so that a signal after a `cancel` is not lost.
            signal->m_promise = owned_ref(mk_mt_promise());
        }

        promise = owned_ref::retain(signal->m_promise.get());
    }

    // Continuations run by the resolve may `stop` a repeating signal and free it, so nothing below may
    // touch it. Code holding the promise may have resolved it already.
    if (!promise_is_resolved(promise.get())) {
        lean_dec(lean_io_promise_resolve(lean_box(signum), promise.get()));
    }

    // Released only after resolving: when the loop holds the last reference this runs the finalizer,
    // which must not drop a pending promise. A one-shot signal is already finished, so continuations
    // run by the resolve cannot have released this reference.
    if (release_loop_ref) {
        lean_dec(obj);
    }
}

/* Std.Internal.UV.Signal.mk (signum : Int32) (repeating : Bool) : IO Signal */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_mk(uint32_t signum_obj, uint8_t repeating) {
    int signum = (int)(int32_t)signum_obj;

    // See `Signal.toInt32` in Std.Async.Signal
    switch (signum) {
        case 1: signum = SIGHUP; break;
        case 2: signum = SIGINT; break;
        case 3: signum = SIGQUIT; break;
        case 6: signum = SIGABRT; break;
        case 15: signum = SIGTERM; break;
        case 28: signum = SIGWINCH; break;
#ifndef LEAN_WINDOWS
        case 5: signum = SIGTRAP; break;
        case 10: signum = SIGUSR1; break;
        case 12: signum = SIGUSR2; break;
        case 14: signum = SIGALRM; break;
        case 17: signum = SIGCHLD; break;
        case 18: signum = SIGCONT; break;
        case 20: signum = SIGTSTP; break;
        case 21: signum = SIGTTIN; break;
        case 22: signum = SIGTTOU; break;
        case 23: signum = SIGURG; break;
        case 24: signum = SIGXCPU; break;
        case 25: signum = SIGXFSZ; break;
        case 26: signum = SIGVTALRM; break;
        case 27: signum = SIGPROF; break;
        case 29: signum = SIGIO; break;
        case 31: signum = SIGSYS; break;
#endif
        default: signum = 0; break;
    }

    lean_uv_signal_object * signal = new (std::nothrow) lean_uv_signal_object;
    if (signal == nullptr) {
        return io_result_mk_enomem();
    }
    signal->m_signum = signum;
    signal->m_lean_signum = (int)(int32_t)signum_obj;
    signal->m_repeating = repeating;

    int result;

    {
        event_loop_guard guard;
        result = uv_signal_init(global_ev.m_loop, &signal->m_uv_signal);
    }

    if (result != 0) {
        delete signal;
        return io_result_mk_uv_error(result);
    }

    lean_object * obj = lean_uv_signal_new(signal);
    lean_mark_mt(obj);
    signal->m_uv_signal.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Signal.next (signal : @& Signal) : IO (IO.Promise Int) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_next(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    owned_ref promise;
    // A promise the signal lets go of: a settled one being replaced, or the one of a failed start.
    owned_ref dropped;
    int result = 0;

    {
        event_loop_guard guard;

        if (signal->m_state == signal_state::Initial) {
            signal->m_promise = owned_ref(mk_mt_promise());

            if (signal->m_repeating) {
                result = uv_signal_start(&signal->m_uv_signal, handle_signal_event, signal->m_signum);
            } else {
                result = uv_signal_start_oneshot(&signal->m_uv_signal, handle_signal_event, signal->m_signum);
            }

            if (result == 0) {
                signal->m_state = signal_state::Running;
                // The event loop keeps the signal alive while a promise is pending.
                lean_inc(obj);
            } else {
                // A failed start must not leave the signal advertising a promise the loop will settle.
                dropped = std::move(signal->m_promise);
            }
        } else if (signal->m_state == signal_state::Running &&
                   (signal->m_repeating ? signal_promise_is_finished(signal) : signal->m_promise.get() == nullptr)) {
            // The loop holds a reference exactly while a promise is pending.
            bool const loop_ref = signal->m_promise.get() != nullptr;
            dropped = std::move(signal->m_promise);

            if (signal->m_received) {
                // A signal that arrived with no promise pending resolves this one at once, so the
                // signal keeps no promise and the loop no reference.
                signal->m_received = false;
                promise = owned_ref(mk_mt_promise());
                lean_dec(lean_io_promise_resolve(lean_box(signal->m_lean_signum), promise.get()));
                if (loop_ref) {
                    lean_dec(obj);
                }
            } else {
                if (!loop_ref) {
                    // A delivery or `cancel` released the loop's reference along with the promise.
                    lean_inc(obj);
                }
                signal->m_promise = owned_ref(mk_mt_promise());
            }
        }

        if (promise.get() == nullptr && signal->m_promise.get() != nullptr) {
            promise = owned_ref::retain(signal->m_promise.get());
        }
    }

    if (result != 0) {
        return io_result_mk_uv_error(result);
    }

    // Without a promise, `stop` dropped this signal's promise, so the fresh one is never resolved.
    return lean_io_result_mk_ok(promise.get() != nullptr ? promise.release() : mk_mt_promise());
}

/* Std.Internal.UV.Signal.stop (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    // Dropping the last reference to the promise resolves its result task with `none` and runs any
    // `(sync := true)` continuation inline on this thread. `Promise.result!` blocks forever on `none`,
    // so this must happen after the unlock: otherwise a waiter on a stopped signal would freeze the
    // whole event loop instead of just itself.
    owned_ref promise;
    int result = 0;

    {
        // Locked so that a firing one-shot signal cannot finish it concurrently.
        event_loop_guard guard;

        if (signal->m_state == signal_state::Running) {
            result = uv_signal_stop(&signal->m_uv_signal);
            promise = std::move(signal->m_promise);
            signal->m_state = signal_state::Finished;
        }
    }

    // The loop holds a reference only while a promise is pending.
    if (promise.get() != nullptr) {
        lean_dec(obj);
    }

    if (result != 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Signal.cancel (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_cancel(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    // Released after the state change and outside the lock, since dropping the last reference runs
    // continuations inline, which may re-enter this handle.
    owned_ref promise;

    {
        // It's locking here to avoid changing the state during other operations.
        event_loop_guard guard;

        // The signal keeps listening, so one that arrives before the next `next` is not lost. The loop
        // stops keeping it alive, so a signal that is dropped instead is closed by its finalizer.
        if (signal->m_state == signal_state::Running && signal->m_promise.get() != nullptr) {
            promise = std::move(signal->m_promise);
        }
    }

    // The loop holds a reference only while a promise is pending.
    if (promise.get() != nullptr) {
        lean_dec(obj);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

#else

/* Std.Internal.UV.Signal.mk (signum : Int32) (repeating : Bool) : IO Signal */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_mk(uint32_t signum_obj, uint8_t repeating) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

/* Std.Internal.UV.Signal.next (signal : @& Signal) : IO (IO.Promise Int) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_next(b_obj_arg signal) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

/* Std.Internal.UV.Signal.stop (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg signal) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

/* Std.Internal.UV.Signal.cancel (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_cancel(b_obj_arg obj) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif

}
