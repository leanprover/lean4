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

// Event loop structure for managing asynchronous events and synchronization across multiple threads.
typedef struct {
    uv_loop_t  * loop;      // The libuv event loop.
    uv_mutex_t   mutex;     // Mutex for protecting `loop`.
    uv_cond_t    cond_var;  // Condition variable for signaling that `loop` is free.
    uv_async_t   async;     // Async handle to interrupt `loop`.
    _Atomic(int) n_waiters; // Atomic counter for managing waiters for `loop`.
} event_loop_t;

/* Rules for releasing Lean objects from the handle wrappers in `runtime/uv`. They are stated here
   rather than at each site that depends on them. (`Timer.stop` and `Signal.stop` follow them since
   #14793.)

   1. Releasing a `lean_object` can run arbitrary Lean code. Resolving a promise, and dropping the
      last reference to an unresolved one, both hand control to the task manager, and a
      `(sync := true)` continuation then runs inline on the releasing thread. Such a continuation may
      re-enter the same handle and may drop its last reference. So a callback or a `cancel` must
      finish mutating the wrapper -- clear its fields, stop the handle -- *before* it releases
      anything, and must not touch the wrapper afterwards.

   2. Releases must happen outside the loop lock. A continuation reached from `lean_dec` can block,
      e.g. a `Promise.result!` waiter on a dropped promise, or one waiting on a `Std.Mutex` held by a
      thread parked in `event_loop_lock`; every other thread would then wait on the lock we hold.
      Callbacks cannot follow this rule: they run inside `uv_run`, which holds the lock. */

// The multithreaded event loop object for all tasks in the task manager.
extern event_loop_t global_ev;

// =======================================
// Event loop manipulation functions.
void event_loop_init(event_loop_t *event_loop);
void event_loop_cleanup(event_loop_t *event_loop);
void event_loop_lock(event_loop_t *event_loop);
void event_loop_unlock(event_loop_t *event_loop);
void event_loop_run_loop(event_loop_t *event_loop);

#endif

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options);
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive();

// Helpers

void lean_promise_resolve_with_code(int status, obj_arg promise);

}
