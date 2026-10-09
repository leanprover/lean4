/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/uv/signal.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

// The finalizer of the `Signal`.
void lean_uv_signal_finalizer(void* ptr) {
    lean_uv_signal_object * signal = (lean_uv_signal_object*) ptr;

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*)signal->m_uv_signal, [](uv_handle_t* handle) {
        free(handle);
    });

    lean_object * promise = signal->m_promise;

    event_loop_unlock(&global_ev);

    if (promise != NULL) {
        lean_dec(promise);
    }

    free(signal);
}

void initialize_libuv_signal() {
    g_uv_signal_external_class = lean_register_external_class(lean_uv_signal_finalizer, [](void* obj, lean_object* f) {
        lean_object* promise = ((lean_uv_signal_object*)obj)->m_promise;

        if (promise != NULL) {
            lean_inc(f);
            lean_inc(promise);
            lean_dec(lean_apply_1(f, promise));
        }
    });
}

static lean_object * create_signal_promise() {
    lean_object * promise = lean_io_promise_new();
    // The loop thread resolves and releases it, so its refcount has to be atomic.
    mark_mt(promise);
    return promise;
}

static bool signal_promise_is_finished(lean_uv_signal_object * signal) {
    return signal->m_promise == NULL || promise_is_resolved(signal->m_promise);
}

void handle_signal_event(uv_signal_t* handle, int) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);
    // Read before `lean_dec(obj)` below may free the signal.
    int const signum = signal->m_lean_signum;

    lean_assert(signal->m_state == SIGNAL_STATE_RUNNING);

    if (signal->m_repeating) {
        if (signal_promise_is_finished(signal)) {
            // Kept for the next `next`, so that a signal between two waits is not lost.
            signal->m_received = true;
        } else {
            // Resolving runs `(sync := true)` continuations inline, which may `cancel` or `stop` the
            // signal and release the field's reference.
            lean_object * promise = signal->m_promise;
            lean_inc(promise);
            lean_object* res = lean_io_promise_resolve(lean_box(signum), promise);
            lean_dec(res);
            lean_dec(promise);
        }
    } else {
        uv_signal_stop(signal->m_uv_signal);
        signal->m_state = SIGNAL_STATE_FINISHED;

        // Without a pending promise the loop holds no reference. The signal is still alive, since
        // its finalizer closes the handle under the loop lock that this callback runs under.
        bool const loop_ref = signal->m_promise != NULL;
        if (!loop_ref) {
            // Kept for the next `next`, so that a signal after a `cancel` is not lost.
            signal->m_promise = create_signal_promise();
        }

        lean_object * promise = signal->m_promise;
        lean_inc(promise);

        if (loop_ref) {
            lean_dec(obj);
        }

        // The signal may be freed by now, so nothing below may touch it. Code holding the promise may
        // have resolved it already.
        if (!promise_is_resolved(promise)) {
            lean_object* res = lean_io_promise_resolve(lean_box(signum), promise);
            lean_dec(res);
        }
        lean_dec(promise);
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

    lean_uv_signal_object * signal = (lean_uv_signal_object*)malloc(sizeof(lean_uv_signal_object));
    if (signal == nullptr) {
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }
    signal->m_signum = signum;
    signal->m_lean_signum = (int)(int32_t)signum_obj;
    signal->m_repeating = repeating;
    signal->m_received = false;
    signal->m_state = SIGNAL_STATE_INITIAL;
    signal->m_promise = NULL;

    uv_signal_t * uv_signal = (uv_signal_t*)malloc(sizeof(uv_signal_t));
    if (uv_signal == nullptr) {
        free(signal);
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }

    event_loop_lock(&global_ev);
    int result = uv_signal_init(global_ev.loop, uv_signal);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(uv_signal);
        free(signal);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    signal->m_uv_signal = uv_signal;

    lean_object * obj = lean_uv_signal_new(signal);
    lean_mark_mt(obj);
    signal->m_uv_signal->data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Signal.next (signal : @& Signal) : IO (IO.Promise Int) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_next(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    auto setup_signal = [obj, signal]() {
        lean_assert(signal->m_promise == NULL);

        lean_object* promise = create_signal_promise();
        signal->m_promise = promise;
        signal->m_state = SIGNAL_STATE_RUNNING;

        // The event loop must keep the signal alive for the duration of the run time.
        lean_inc(obj);
        lean_inc(promise);

        int result;
        if (signal->m_repeating) {
            result = uv_signal_start(
                signal->m_uv_signal,
                handle_signal_event,
                signal->m_signum
            );
        } else {
            result = uv_signal_start_oneshot(
                signal->m_uv_signal,
                handle_signal_event,
                signal->m_signum
            );
        }

        if (result != 0) {
            // A failed start must not leave the signal advertising a promise the loop will settle.
            signal->m_state = SIGNAL_STATE_INITIAL;
            signal->m_promise = NULL;

            lean_dec(promise); // The structure does not own it.
            lean_dec(promise); // We are not going to return it.
            lean_dec(obj);

            event_loop_unlock(&global_ev);
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        }

        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(promise);
    };

    event_loop_lock(&global_ev);

    if (signal->m_repeating) {
        switch (signal->m_state) {
            case SIGNAL_STATE_INITIAL:
                {
                    return setup_signal();
                }
            case SIGNAL_STATE_RUNNING:
                {
                    if (signal_promise_is_finished(signal)) {
                        if (signal->m_promise != NULL) {
                            lean_dec(signal->m_promise);
                        } else {
                            // `cancel` released the loop's reference along with the promise.
                            lean_inc(obj);
                        }

                        signal->m_promise = create_signal_promise();

                        if (signal->m_received) {
                            signal->m_received = false;
                            lean_dec(lean_io_promise_resolve(lean_box(signal->m_lean_signum), signal->m_promise));
                        }
                    }

                    lean_object * promise = signal->m_promise;
                    lean_inc(promise);
                    event_loop_unlock(&global_ev);
                    return lean_io_result_mk_ok(promise);
                }
            case SIGNAL_STATE_FINISHED:
                {
                    if (signal->m_promise == NULL) {
                        lean_object* finished_promise = create_signal_promise();
                        event_loop_unlock(&global_ev);
                        return lean_io_result_mk_ok(finished_promise);
                    }

                    lean_object * promise = signal->m_promise;
                    lean_inc(promise);
                    event_loop_unlock(&global_ev);
                    return lean_io_result_mk_ok(promise);
                }
        }
    } else {
        if (signal->m_state == SIGNAL_STATE_INITIAL) {
            return setup_signal();
        } else if (signal->m_state == SIGNAL_STATE_RUNNING && signal->m_promise == NULL) {
            // Still listening after a `cancel`, which released the loop's reference.
            lean_inc(obj);
            lean_object * promise = create_signal_promise();
            signal->m_promise = promise;
            lean_inc(promise);
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(promise);
        } else if (signal->m_promise != NULL) {
            lean_object * promise = signal->m_promise;
            lean_inc(promise);
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(promise);
        } else {
            lean_object* finished_promise = create_signal_promise();
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(finished_promise);
        }
    }
}

/* Std.Internal.UV.Signal.stop (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    // Locked so that a firing one-shot signal cannot finish it concurrently.
    event_loop_lock(&global_ev);

    if (signal->m_state != SIGNAL_STATE_RUNNING) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(lean_box(0));
    }

    int result = uv_signal_stop(signal->m_uv_signal);
    lean_object * promise = signal->m_promise;
    signal->m_promise = NULL;
    signal->m_state = SIGNAL_STATE_FINISHED;

    event_loop_unlock(&global_ev);

    // This dec can drop the last reference to the promise, which resolves its result task
    // with `none` and runs any `(sync := true)` continuation inline on this thread.
    // `Promise.result!` blocks forever on `none`, so this must happen after the unlock:
    // otherwise a waiter on a stopped signal would freeze the whole event loop instead of
    // just itself.
    if (promise != NULL) {
        lean_dec(promise);
        // The loop holds a reference only while a promise is pending.
        lean_dec(obj);
    }

    if (result != 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Signal.cancel (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_cancel(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    // It's locking here to avoid changing the state during other operations.
    event_loop_lock(&global_ev);

    lean_object * promise = NULL;

    // The signal keeps listening, so one that arrives before the next `next` is not lost. The loop
    // stops keeping it alive, so a signal that is dropped instead is closed by its finalizer.
    if (signal->m_state == SIGNAL_STATE_RUNNING && signal->m_promise != NULL) {
        promise = signal->m_promise;
        signal->m_promise = NULL;
    }

    event_loop_unlock(&global_ev);

    // Released after the state change and outside the lock, since dropping the last reference
    // runs continuations inline, which may re-enter this handle.
    if (promise != NULL) {
        lean_dec(promise);
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
