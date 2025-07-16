/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/signal.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN

using namespace std;

typedef struct {
    uv_signal_t signal;
    lean_object* promise;
} signal_req_t;

/* Std.Internal.UV.Signal.wait (signum : Int) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_wait(lean_obj_arg signum_obj, obj_arg /* w */) {
    int signum = lean_scalar_to_int(signum_obj);

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    signal_req_t* req = (signal_req_t*)malloc(sizeof(signal_req_t));
    req->promise = promise;
    req->signal.data = req;

    lean_inc(promise); // Says that it's owned by the event loop too.
    event_loop_lock(&global_ev);

    int result = uv_signal_init(global_ev.loop, &req->signal);

    if (result < 0) {
        event_loop_unlock(&global_ev);
        lean_dec(promise);
        lean_dec(promise);
        free(req);
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    result = uv_signal_start_oneshot(&req->signal, [](uv_signal_t *handle, int signum) {
        signal_req_t* req = (signal_req_t*)handle->data;

        lean_object* unit_val = lean_box(0);
        lean_promise_resolve(mk_except_ok(unit_val), req->promise);

        lean_dec(req->promise);

        uv_close((uv_handle_t*)handle, [](uv_handle_t* handle) {
            signal_req_t* req = (signal_req_t*)handle->data;
            free(req);
        });
    }, signum);

    event_loop_unlock(&global_ev);

    if (result < 0) {
        lean_dec(promise);
        lean_dec(promise);
        uv_close((uv_handle_t*)&req->signal, [](uv_handle_t* handle) {
            signal_req_t* req = (signal_req_t*)handle->data;
            free(req);
        });
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(promise);
}

#else

/* Std.Internal.UV.Signal.wait (signum : Int) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_wait(lean_obj_arg signum_obj, obj_arg /* w */) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif

}