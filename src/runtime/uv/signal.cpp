/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/uv/signal.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

void lean_uv_signal_finalizer(void* ptr) {
    lean_uv_signal_object* signal = (lean_uv_signal_object*) ptr;

    if (!event_loop_lock(&global_ev)) {
        event_loop_wait_finalized(&global_ev);
        if (signal->m_uv_signal != nullptr) {
            free(signal->m_uv_signal);
        }

        free(signal);
        return;
    }

    if (signal->m_promise != NULL) {
        lean_dec(signal->m_promise);
    }

    uv_close((uv_handle_t*)signal->m_uv_signal, [](uv_handle_t* handle) {
        free(handle);
    });

    event_loop_unlock(&global_ev);

    free(signal);
}

void initialize_libuv_signal() {
    g_uv_signal_external_class = lean_register_external_class(lean_uv_signal_finalizer, [](void* obj, lean_object* f) {
        lean_object * promise = ((lean_uv_signal_object*)obj)->m_promise;

        if (promise != NULL) {
            lean_inc(f);
            lean_inc(promise);
            lean_dec(lean_apply_1(f, promise));
        }
    });
}

static bool signal_promise_is_finished(lean_uv_signal_object * signal) {
    return signal->m_promise == NULL || promise_is_resolved(signal->m_promise);
}

void handle_signal_event(uv_signal_t* handle, int signum) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    lean_assert(signal->m_state == SIGNAL_STATE_RUNNING);

    if (signal->m_repeating) {
        if (!signal_promise_is_finished(signal)) {
            // Resolving runs Lean code: a `(sync := true)` continuation runs on this thread and a
            // `cancel` from it drops the promise the loop is still resolving, so hold a reference
            // across the call. `signal` must not be touched afterwards for the same reason.
            lean_object* promise = signal->m_promise;
            lean_inc(promise);

            lean_object* res = lean_io_promise_resolve(mk_except_ok(lean_box(signum)), promise);
            lean_dec(res);
            lean_dec(promise);
        }
    } else {
        uv_signal_stop(signal->m_uv_signal);
        signal->m_state = SIGNAL_STATE_FINISHED;

        lean_object * promise = signal->m_promise;
        if (promise != NULL) {
            lean_inc(promise);
        }

        lean_dec(obj);

        // Resolving runs Lean code: a `(sync := true)` continuation runs on this thread and may
        // drop the last reference to the signal, so neither `signal` nor `obj` may be touched below.
        if (promise != NULL) {
            lean_object* res = lean_io_promise_resolve(mk_except_ok(lean_box(signum)), promise);
            lean_dec(res);
            lean_dec(promise);
        }
    }
}

size_t lean_uv_signal_shutdown(lean_uv_signal_object * signal, uv_deferred_teardown & deferred) {
    size_t release_refs = 0;

    if (signal->m_state == SIGNAL_STATE_RUNNING) {
        // `cancel` on a repeating signal leaves it running without a promise, in which case the loop
        // has already given its reference back.
        if (signal->m_promise != NULL) {
            release_refs += 1;
        }

        uv_signal_stop(signal->m_uv_signal);
        signal->m_state = SIGNAL_STATE_FINISHED;
    }

    if (signal->m_promise != NULL) {
        deferred.cancel_promise(signal->m_promise);
        signal->m_promise = NULL;
    }

    signal->m_uv_signal = nullptr;
    return release_refs;
}

/* Std.Internal.UV.Signal.mk (signum : Int32) (repeating : Bool) : IO Signal */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_mk(uint32_t signum_obj, uint8_t repeating) {
    int signum = (int)(int32_t)signum_obj;

    // See toInt32 in Std.Internal.IO.Async.Signal
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
    uv_signal_t * uv_signal = (uv_signal_t*)malloc(sizeof(uv_signal_t));
    if (uv_signal == nullptr) {
        free(signal);
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }

    signal->m_uv_signal = uv_signal;
    signal->m_signum = signum;
    signal->m_repeating = repeating;
    signal->m_state = SIGNAL_STATE_INITIAL;
    signal->m_promise = NULL;

    if (!event_loop_lock(&global_ev)) {
        free(uv_signal);
        free(signal);
        return lean_uv_loop_unavailable_error();
    }
    int result = uv_signal_init(global_ev.loop, uv_signal);

    if (result != 0) {
        event_loop_unlock(&global_ev);
        free(uv_signal);
        free(signal);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    lean_object * obj = lean_uv_signal_new(signal);
    lean_mark_mt(obj);
    signal->m_uv_signal->data = obj;

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.Signal.next (signal : @& Signal) : IO (IO.Promise Int) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_next(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    auto create_promise = []() {
        lean_object * promise = lean_io_promise_new();
        // The loop thread resolves and releases it, so its refcount has to be atomic.
        mark_mt(promise);
        return promise;
    };

    auto setup_signal = [create_promise, obj, signal]() {
        lean_assert(signal->m_promise == NULL);

        lean_object* promise = create_promise();
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
            // Restore the pre-call state: leaving `RUNNING` behind would make the teardown walk
            // believe the loop still holds the reference released just below.
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

    if (!event_loop_lock(&global_ev)) {
        return lean_uv_loop_unavailable_error();
    }

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
                            // Re-arming after `cancel`: the loop owes a promise again, so it takes
                            // its reference on the signal back.
                            lean_inc(obj);
                        }

                        signal->m_promise = create_promise();
                    }

                    lean_object* promise = signal->m_promise;
                    lean_inc(promise);
                    event_loop_unlock(&global_ev);
                    return lean_io_result_mk_ok(promise);
                }
            case SIGNAL_STATE_FINISHED:
                {
                    if (signal->m_promise == NULL) {
                        lean_object* finished_promise = create_promise();
                        event_loop_unlock(&global_ev);
                        return lean_io_result_mk_ok(finished_promise);
                    }

                    lean_object* promise = signal->m_promise;
                    lean_inc(promise);
                    event_loop_unlock(&global_ev);
                    return lean_io_result_mk_ok(promise);
                }
        }
    } else {
        if (signal->m_state == SIGNAL_STATE_INITIAL) {
            return setup_signal();
        } else if (signal->m_promise != NULL) {
            lean_object* promise = signal->m_promise;
            lean_inc(promise);
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(promise);
        } else {
            lean_object* finished_promise = create_promise();
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(finished_promise);
        }
    }
}

/* Std.Internal.UV.Signal.stop (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    // `m_state` is shared with the loop thread, so it may only be read under the lock.
    if (!event_loop_lock(&global_ev)) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    if (signal->m_state != SIGNAL_STATE_RUNNING) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(lean_box(0));
    }

    int result = uv_signal_stop(signal->m_uv_signal);

    // `cancel` on a repeating signal leaves it running without a promise, in which case the loop
    // has already given its reference back and must not be charged for it twice.
    bool loop_owns_signal = signal->m_promise != NULL;

    lean_object * promise = signal->m_promise;
    signal->m_promise = NULL;
    signal->m_state = SIGNAL_STATE_FINISHED;

    event_loop_unlock(&global_ev);

    // Dropping the last reference to an unresolved promise resolves it, which runs Lean code
    // that may re-enter this signal, so the stop has to be complete before any release below.
    if (promise != NULL) {
        lean_dec(promise);
    }

    if (loop_owns_signal) {
        // The loop does not need to keep the signal alive anymore.
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
    if (!event_loop_lock(&global_ev)) {
        return lean_io_result_mk_ok(lean_box(0));
    }

    lean_object * promise = NULL;

    if (signal->m_state == SIGNAL_STATE_RUNNING && signal->m_promise != NULL) {
        promise = signal->m_promise;
        signal->m_promise = NULL;

        // A repeating signal keeps its handler installed, it just no longer owes anyone a promise.
        // Either way the loop gives its reference back; otherwise a dropped repeating signal could
        // never be reclaimed, as the reference kept it alive and only it could have released the
        // reference.
        if (!signal->m_repeating) {
            uv_signal_stop(signal->m_uv_signal);
            signal->m_state = SIGNAL_STATE_INITIAL;
        }
    }

    event_loop_unlock(&global_ev);

    // Dropping the last reference to an unresolved promise resolves it, which runs Lean code that
    // may re-enter this signal, so the cancellation has to be complete before any release below.
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
