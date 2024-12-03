/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/alloc.h"
#include "runtime/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"
#include "runtime/object.h"

namespace lean {

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

typedef struct {
    uv_timer_t    m_uv_timer;
    lean_object * m_promise;
    uint64_t      m_timeout;
    bool          m_repeating;
    bool          m_started;
} lean_uv_timer_object;

static lean_external_class * g_uv_timer_external_class = NULL;

inline static void noop_foreach(void * mod, b_lean_obj_arg fn) {}

// =======================================
// Timer object manipulation functions.
static inline lean_object* lean_uv_timer_new(lean_uv_timer_object * s) { return lean_alloc_external(g_uv_timer_external_class, s); }
static inline lean_uv_timer_object* lean_to_uv_timer(lean_object * o) { return (lean_uv_timer_object*)(lean_get_external_data(o)); }

#endif

extern "C" void initialize_libuv();

// =======================================
// General LibUV functions.
extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg);

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options, obj_arg /* w */ );
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(obj_arg /* w */ );

// =======================================
// Timer manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(uint64_t timeout, uint8_t repeating, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */);

}