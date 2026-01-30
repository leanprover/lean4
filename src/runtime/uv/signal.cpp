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

    if (signal->m_promise != NULL) {
        lean_dec(signal->m_promise);
    }

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*)signal->m_uv_signal, [](uv_handle_t* handle) {
        free(handle);
    });

    event_loop_unlock(&global_ev);

    free(signal);
}

void initialize_libuv_signal() {
    g_uv_signal_external_class = lean_register_external_class(lean_uv_signal_finalizer, [](void* obj, lean_object* f) {
        if (((lean_uv_signal_object*)obj)->m_promise != NULL) {
            lean_inc(f);
            lean_apply_1(f, ((lean_uv_signal_object*)obj)->m_promise);
        }
    });
}

static bool signal_promise_is_finished(lean_uv_signal_object * signal) {
    return signal->m_promise == NULL || lean_io_get_task_state_core((lean_object *)lean_to_promise(signal->m_promise)->m_result) == 2;
}

void handle_signal_event(uv_signal_t* handle, int signum) {
    lean_object * obj = (lean_object*)handle->data;
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    lean_assert(signal->m_state == SIGNAL_STATE_RUNNING);

    if (signal->m_repeating) {
        if (!signal_promise_is_finished(signal)) {
            lean_object* res = lean_io_promise_resolve(lean_box(signum), signal->m_promise);
            lean_dec(res);
        }
    } else {
        if (signal->m_promise != NULL) {
            lean_object* res = lean_io_promise_resolve(lean_box(signum), signal->m_promise);
            lean_dec(res);
        }

        uv_signal_stop(signal->m_uv_signal);
        signal->m_state = SIGNAL_STATE_FINISHED;

        lean_dec(obj);
    }
}

/* Std.Internal.UV.Signal.mk (signum : Int32) (repeating : Bool) : IO Signal */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_mk(uint32_t signum_obj, uint8_t repeating) {
    int signum = (int)(int32_t)signum_obj;

    lean_uv_signal_object * signal = (lean_uv_signal_object*)malloc(sizeof(lean_uv_signal_object));
    signal->m_signum = signum;
    signal->m_repeating = repeating;
    signal->m_state = SIGNAL_STATE_INITIAL;
    signal->m_promise = NULL;

    uv_signal_t * uv_signal = (uv_signal_t*)malloc(sizeof(uv_signal_t));

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

        lean_object* promise = lean_io_promise_new();
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
            lean_dec(obj);
            lean_dec(promise);
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
                        }

                        signal->m_promise = lean_io_promise_new();
                    }

                    lean_inc(signal->m_promise);
                    event_loop_unlock(&global_ev);
                    return lean_io_result_mk_ok(signal->m_promise);
                }
            case SIGNAL_STATE_FINISHED:
                {
                    if (signal->m_promise == NULL) {
                        lean_object* finished_promise = lean_io_promise_new();
                        event_loop_unlock(&global_ev);
                        return lean_io_result_mk_ok(finished_promise);
                    }

                    lean_inc(signal->m_promise);
                    event_loop_unlock(&global_ev);
                    return lean_io_result_mk_ok(signal->m_promise);
                }
        }
    } else {
        if (signal->m_state == SIGNAL_STATE_INITIAL) {
            return setup_signal();
        } else if (signal->m_promise != NULL) {
            lean_inc(signal->m_promise);
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(signal->m_promise);
        } else {
            lean_object* finished_promise = lean_io_promise_new();
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_ok(finished_promise);
        }
    }
}

/* Std.Internal.UV.Signal.stop (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    if (signal->m_state == SIGNAL_STATE_RUNNING) {
        event_loop_lock(&global_ev);
        int result = uv_signal_stop(signal->m_uv_signal);
        event_loop_unlock(&global_ev);

        if  (signal->m_promise != NULL) {
            lean_dec(signal->m_promise);
            signal->m_promise = NULL;
        }

        signal->m_state = SIGNAL_STATE_FINISHED;

        // The loop does not need to keep the signal alive anymore.
        lean_dec(obj);

        if (result != 0) {
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        } else {
            return lean_io_result_mk_ok(lean_box(0));
        }
    } else {
        return lean_io_result_mk_ok(lean_box(0));
    }
}

/* Std.Internal.UV.Signal.cancel (signal : @& Signal) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_cancel(b_obj_arg obj) {
    lean_uv_signal_object * signal = lean_to_uv_signal(obj);

    // It's locking here to avoid changing the state during other operations.
    event_loop_lock(&global_ev);

    if (signal->m_state == SIGNAL_STATE_RUNNING && signal->m_promise != NULL) {
        if (signal->m_repeating) {
            lean_dec(signal->m_promise);
            signal->m_promise = NULL;
        } else {
            uv_signal_stop(signal->m_uv_signal);
            lean_dec(signal->m_promise);
            signal->m_promise = NULL;
            signal->m_state = SIGNAL_STATE_INITIAL;
            lean_dec(obj);
        }
    }

    event_loop_unlock(&global_ev);
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
