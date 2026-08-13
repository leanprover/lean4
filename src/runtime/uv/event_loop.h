/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <vector>
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
    EVENT_LOOP_FINALIZED,
};

/* Rules that every handle wrapper in `runtime/uv` follows. They are stated here rather than at each
   of the ~30 sites that depend on them.

   1. Releasing a `lean_object` can run arbitrary Lean code. Resolving a promise, and dropping the
      last reference to an unresolved one, both hand control to the task manager, and a
      `(sync := true)` continuation then runs inline on the releasing thread. Such a continuation may
      re-enter the same handle and may drop its last reference. So a callback or a `cancel`/`stop`
      must finish mutating the wrapper -- clear the promise field, stop the handle, hand the loop's
      reference back -- *before* it releases anything, and must not touch the wrapper afterwards.

   2. Releases must happen outside the loop lock. A continuation reached from `lean_dec` can block on
      a `Std.Mutex` held by a thread parked in `event_loop_lock`, which would then be waiting on the
      lock we hold.

   3. Teardown cannot release anything at all while it walks the loop, so it collects into a
      `uv_deferred_teardown` and drains that once the walk is done and the lock is dropped.

   4. `handle->data` points at the wrapper and is what the teardown walk reads to find it. libuv
      leaves `data` untouched by `uv_*_init`, so it has to be set before the handle reaches the loop,
      and every constructor publishes it before releasing the lock. */
class uv_deferred_teardown {
    std::vector<lean_object *> m_objects;

public:
    // Pending promises are released rather than settled: dropping the last reference to an
    // unresolved promise resolves its task to `none`, which `Async.ofPromise` and friends already
    // report as a failure. This is the same path `stop` and `cancel` take.
    void release(lean_object * obj) { m_objects.push_back(obj); }

    void run();
};

// A libuv request that is bound to the loop rather than to a handle: DNS resolution and
// `uv_random`. `uv_walk` only visits handles, so these are tracked in an intrusive list in order to
// be cancelled during teardown; without it `finalize_libuv` would block until they complete, which
// a slow resolver can delay indefinitely.
typedef struct uv_pending_req {
    uv_req_t * req;
    lean_object * promise;
    lean_object * owned;
    struct uv_pending_req * next;
    struct uv_pending_req * prev;
} uv_pending_req;

// Event loop structure for managing asynchronous events and synchronization across multiple threads.
typedef struct {
    uv_loop_t  * loop;             // The libuv event loop, owned by the runtime.
    uv_mutex_t   mutex;            // Mutex for protecting `loop`.
    uv_mutex_t   interrupt_mutex;  // Mutex for protecting `async` against the teardown that closes it.
    uv_mutex_t   finalize_mutex;   // Mutex for `finalize_cond`; separate because `mutex` is recursive.
    uv_cond_t    cond_var;         // Condition variable for signaling that `loop` is free.
    uv_cond_t    finalize_cond;    // Condition variable broadcast once the loop has been finalized.
    uv_async_t   async;            // Async handle to interrupt `loop`.
    _Atomic(int) n_waiters;        // Atomic counter for managing waiters for `loop`.
    _Atomic(int) state;            // Current event_loop_state.
    uv_pending_req * requests;     // Loop-bound requests not visible to `uv_walk`; guarded by `mutex`.
} event_loop_t;

// The multithreaded event loop object for all tasks in the task manager.
//
// `loop` is a loop the runtime owns outright, deliberately not `uv_default_loop()`. `finalize_libuv`
// enumerates it with `uv_walk` and reaps everything it finds, and a `uv_handle_t` carries nothing
// that identifies its owner -- `data` belongs to whoever created the handle -- so a foreign handle
// of a type the teardown recognises would be read as a Lean wrapper and then freed. The default loop
// is a process-wide singleton that any other libuv user in the binary may put handles on, which is
// exactly what this must not share.
extern event_loop_t global_ev;

// =======================================
// Event loop manipulation functions.
void event_loop_init(event_loop_t *event_loop);
bool event_loop_lock(event_loop_t *event_loop);
void event_loop_lock_internal(event_loop_t *event_loop);
void event_loop_unlock(event_loop_t *event_loop);
void event_loop_request_stop(event_loop_t *event_loop);
void event_loop_begin_teardown();
void event_loop_mark_finalized(event_loop_t *event_loop);
void event_loop_wait_finalized(event_loop_t *event_loop);
lean_obj_res lean_uv_loop_unavailable_error();
void event_loop_register_request(event_loop_t *event_loop, uv_pending_req *pending, uv_req_t *req, lean_object *promise, lean_object *owned);
void event_loop_unregister_request(event_loop_t *event_loop, uv_pending_req *pending);
void event_loop_cancel_requests(event_loop_t *event_loop);
bool event_loop_abandon_requests(event_loop_t *event_loop, uv_deferred_teardown &deferred);
void event_loop_run_loop(event_loop_t *event_loop);

#endif

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options);
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive();

// Helpers

void lean_promise_resolve_with_code(int status, b_obj_arg promise);

}
