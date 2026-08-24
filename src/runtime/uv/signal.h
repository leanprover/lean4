/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

static lean_external_class * g_uv_signal_external_class = NULL;
void initialize_libuv_signal();

#ifndef LEAN_EMSCRIPTEN
using namespace std;

enum uv_signal_state {
    SIGNAL_STATE_INITIAL,
    SIGNAL_STATE_RUNNING,
    SIGNAL_STATE_FINISHED,
};

// Structure for managing a single UV signal object, including promise handling, signal number, and
// repeating behavior. The repeating behavior exists to "set" a handler and avoid it not getting signals
// between the creation of oneshot signal handlers.
typedef struct {
    uv_signal_t *   m_uv_signal;   // LibUV signal handle.
    lean_object *   m_promise;     // The associated promise for asynchronous results.
    int             m_signum;      // Signal number to watch for.
    bool            m_repeating;   // Flag indicating if the signal handler is repeating.
    uv_signal_state m_state;       // The state of the signal.
} lean_uv_signal_object;

// `m_promise` may be NULL in any state: `stop` leaves a FINISHED signal without one, and `cancel` on
// a repeating signal leaves it RUNNING without one.
//
// The invariant the reference counting relies on is instead:
//
//     the loop holds exactly one reference on the signal object
//     iff `m_state == SIGNAL_STATE_RUNNING && m_promise != NULL`
//
// which is what every `loop_owns_signal` test and `deferred.release(obj)` below is checking.
// Dropping one of those NULL checks over-releases the handle and frees it while it is still armed.

// =======================================
// Signal object manipulation functions.
static inline lean_object* lean_uv_signal_new(lean_uv_signal_object * s) { return lean_alloc_external(g_uv_signal_external_class, s); }
static inline lean_uv_signal_object* lean_to_uv_signal(lean_object * o) { return (lean_uv_signal_object*)(lean_get_external_data(o)); }

void lean_uv_signal_shutdown(lean_object * obj, uv_deferred_teardown & deferred);

#endif

// =======================================
// Signal manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_mk(uint32_t signum_obj, uint8_t repeating);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_next(b_obj_arg signal);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_stop(b_obj_arg signal);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_signal_cancel(b_obj_arg obj);

}
