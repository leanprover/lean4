/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/libuv.h"
#include "runtime/alloc.h"
#include "runtime/io.h"
#include "runtime/utf8.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/allocprof.h"
#include "runtime/object.h"

using namespace lean;

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>

typedef struct {
    uv_loop_t               m_uv_loop;
    lean_object *           m_io_error;
} lean_uv_event_loop_object;

typedef struct {
    uv_timer_t             m_uv_timer;
    lean_object *          m_promise;
    uint64_t               m_timeout;
} lean_uv_timer_object;

static lean_external_class *g_uv_event_loop_external_class = NULL;
static lean_external_class *g_uv_timer_external_class = NULL;

inline static void noop_foreach(void *mod, b_lean_obj_arg fn) {}

static inline lean_object* lean_uv_event_loop_new(lean_uv_event_loop_object *s) { return lean_alloc_external(g_uv_event_loop_external_class, s); }
static inline lean_object* lean_uv_timer_new(lean_uv_timer_object *s) { return lean_alloc_external(g_uv_timer_external_class, s); }

static inline lean_uv_timer_object* lean_to_uv_timer(lean_object* o) { return (lean_uv_timer_object*)(lean_get_external_data(o)); }
static inline lean_uv_event_loop_object* lean_to_uv_event_loop(lean_object* o) { return (lean_uv_event_loop_object*)(lean_get_external_data(o)); }

#endif

extern "C" lean_obj_res lean_uv_initialize();

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg);

extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_mk(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_run(b_obj_arg loop, uint8_t mode, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg loop, b_obj_arg options, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_close(b_obj_arg loop, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_stop(b_obj_arg loop, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive(b_obj_arg loop, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_now(b_obj_arg loop, obj_arg /* w */);

extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_mk(b_obj_arg loop, uint64_t timeout, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_next(b_obj_arg timer, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_timer_stop(b_obj_arg timer, obj_arg /* w */);