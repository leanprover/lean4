/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

void initialize_libuv_loop();

#ifndef LEAN_EMSCRIPTEN
using namespace std;

enum event_loop_state {
    EVENT_LOOP_UNINITIALIZED,
    EVENT_LOOP_RUNNING,
    EVENT_LOOP_STOPPING,
};

// A libuv request that is bound to the loop rather than to a handle: DNS resolution and
// `uv_random`. `uv_walk` only visits handles, so these are tracked in an intrusive list in order to
// be cancelled when the loop thread stops; without it the threadpool shutdown at exit would first
// run every request still queued.
typedef struct uv_pending_req {
    uv_req_t * req;
    struct uv_pending_req * next;
    struct uv_pending_req * prev;
} uv_pending_req;

// Event loop structure for managing asynchronous events and synchronization across multiple threads.
typedef struct {
    uv_loop_t  * loop;      // The libuv event loop.
    uv_mutex_t   mutex;     // Mutex for protecting `loop`.
    uv_cond_t    cond_var;  // Condition variable for signaling that `loop` is free.
    uv_async_t   async;     // Async handle to interrupt `loop`.
    _Atomic(int) state;     // Current event_loop_state; written under `mutex`.
    uv_pending_req * requests; // Loop-bound requests not visible to `uv_walk`; guarded by `mutex`.
    _Atomic(int) n_waiters; // Atomic counter for managing waiters for `loop`.
} event_loop_t;

// The multithreaded event loop object for all tasks in the task manager.
extern event_loop_t global_ev;

// =======================================
// Event loop manipulation functions.
void event_loop_init(event_loop_t *event_loop);
void event_loop_cleanup(event_loop_t *event_loop);
void event_loop_lock(event_loop_t *event_loop);
void event_loop_unlock(event_loop_t *event_loop);
void event_loop_run_loop(event_loop_t *event_loop);
void event_loop_request_stop(event_loop_t *event_loop);
void event_loop_register_request(event_loop_t *event_loop, uv_pending_req *pending, uv_req_t *req);
void event_loop_unregister_request(event_loop_t *event_loop, uv_pending_req *pending);
void event_loop_cancel_requests(event_loop_t *event_loop);

#endif

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options);
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive();

// Helpers

void lean_promise_resolve_with_code(int status, obj_arg promise);

}
