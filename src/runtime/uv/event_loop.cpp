/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#include "runtime/uv/event_loop.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN
using namespace std;

event_loop_t global_ev;

// Utility function for error checking. This function is only used inside the
// initializition of the event loop.
static void check_uv(int result, const char * msg) {
    if (result != 0) {
        std::string err_message = std::string(msg) + ": " + uv_strerror(result);
        lean_internal_panic(err_message.c_str());
    }
}

// The callback that stops the loop when it's called.
void async_callback(uv_async_t * handle) {
    uv_stop(handle->loop);
}

// Awakes the event loop and stops it so it can receive future requests.
void event_loop_wake(event_loop_t * event_loop) {
    int result = uv_async_send(&event_loop->async);
    (void)result;
    lean_assert(result == 0);
}

// Initializes the event loop
void event_loop_init(event_loop_t * event_loop) {
    event_loop->loop = uv_default_loop();
    check_uv(uv_mutex_init_recursive(&event_loop->mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&event_loop->cond_var), "Failed to initialize condition variable");
    check_uv(uv_async_init(event_loop->loop, &event_loop->async, NULL), "Failed to initialize async");
    event_loop->n_waiters = 0;
}

// Locks the event loop for the side of the requesters.
void event_loop_lock(event_loop_t * event_loop) {
    if (uv_mutex_trylock(&event_loop->mutex) != 0) {
        event_loop->n_waiters++;
        event_loop_wake(event_loop);
        uv_mutex_lock(&event_loop->mutex);
        event_loop->n_waiters--;
    }
}

// Unlock event loop
void event_loop_unlock(event_loop_t * event_loop) {
    uv_mutex_unlock(&event_loop->mutex);
    if (event_loop->n_waiters == 0) {
        uv_cond_signal(&event_loop->cond_var);
    }
}

// Runs the loop and stops when it needs to register new requests.
void event_loop_run_loop(event_loop_t * event_loop) {
    while (uv_loop_alive(event_loop->loop)) {
        uv_mutex_lock(&event_loop->mutex);

        if (event_loop->n_waiters != 0) {
            uv_cond_wait(&event_loop->cond_var, &event_loop->mutex);
        }

        if (event_loop->n_waiters == 0) {
            uv_run(event_loop->loop, UV_RUN_ONCE);
        }

        uv_mutex_unlock(&event_loop->mutex);
    }
}

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ ) {
    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    event_loop_lock(&global_ev);

    if (accum && uv_loop_configure(global_ev.loop, UV_METRICS_IDLE_TIME) != 0) {
        return io_result_mk_error("failed to configure global_ev.loop with UV_METRICS_IDLE_TIME");
    }

    #if!defined(WIN32) && !defined(_WIN32)
    if (block && uv_loop_configure(global_ev.loop, UV_LOOP_BLOCK_SIGNAL, SIGPROF) != 0) {
        return io_result_mk_error("failed to configure global_ev.loop with UV_LOOP_BLOCK_SIGNAL");
    }
    #endif

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Loop.alive : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ ) {
    event_loop_lock(&global_ev);
    int is_alive = uv_loop_alive(global_ev.loop);
    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(lean_box(is_alive));
}

void initialize_libuv_loop() {
    event_loop_init(&global_ev);
}

#else

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ ) {
    return io_result_mk_error("lean_uv_event_loop_configure is not supported");
}

/* Std.Internal.UV.Loop.alive : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ ) {
    return io_result_mk_error("lean_uv_event_loop_alive is not supported");
}

#endif

}
