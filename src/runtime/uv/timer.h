/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"

namespace lean {

static lean_external_class * g_uv_timer_external_class = NULL;
void initialize_libuv_timer();

#ifndef LEAN_EMSCRIPTEN
using namespace std;
#include <uv.h>

enum uv_timer_state {
    TIMER_STATE_INITIAL,
    TIMER_STATE_RUNNING,
    TIMER_STATE_FINISHED,
};

// Structure for managing a single UV timer object, including promise handling, timeout, and
// repeating behavior.
typedef struct {
    uv_timer_t *    m_uv_timer;    // LibUV timer handle.
    lean_object *   m_promise;     // The associated promise for asynchronous results.
    uint64_t        m_timeout;     // Timeout duration in milliseconds.
    bool            m_repeating;   // Flag indicating if the timer is repeating.
    uv_timer_state  m_state;       // The state of the timer. Beyond the API description on the Lean
                                   // side this state has the invariant:
                                   // `m_state != TIMER_STATE_INITIAL` -> `m_promise != NULL`
} lean_uv_timer_object;

// =======================================
// Timer object manipulation functions.
static inline lean_object* lean_uv_timer_new(lean_uv_timer_object * s) { return lean_alloc_external(g_uv_timer_external_class, s); }
static inline lean_uv_timer_object* lean_to_uv_timer(lean_object * o) { return (lean_uv_timer_object*)(lean_get_external_data(o)); }

#else

// =======================================
// Timer manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_reset(b_obj_arg timer, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */);

#endif

}
