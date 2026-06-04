/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/uv/event_loop.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

static lean_external_class * g_uv_process_external_class = NULL;
void initialize_libuv_process();

#ifndef LEAN_EMSCRIPTEN
using namespace std;

// Wrapper for a spawned child process backed by a libuv `uv_process_t`.
//
// libuv reaps the child and invokes the exit callback on the event loop thread. The exit status is
// recorded under `m_mutex`; `lean_io_process_child_wait` blocks on `m_cond` until `m_exited` is set
typedef struct {
    uv_process_t * m_uv_process;    // libuv process handle.
    uv_mutex_t     m_mutex;         // Protects the exit state below.
    uv_cond_t      m_cond;          // Signaled by the exit callback once the child has exited.
    bool           m_exited;        // Whether the child has exited.
    int64_t        m_exit_status;   // Exit code, valid once `m_exited`.
    int            m_term_signal;   // Terminating signal (0 if none), valid once `m_exited`.
    bool           m_setsid;        // Whether the child was started in its own session/process group.
    bool           m_spawned;       // Whether `uv_spawn` succeeded, i.e. `m_uv_process` is a live handle.
} lean_uv_process_object;

static inline lean_object* lean_uv_process_new(lean_uv_process_object * s) {
    return lean_alloc_external(g_uv_process_external_class, s);
}
static inline lean_uv_process_object* lean_to_uv_process(lean_object * o) {
    return (lean_uv_process_object*)(lean_get_external_data(o));
}

#else

// =======================================
// Process manipulation functions
extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args);
extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg world, b_obj_arg child);
extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg world, b_obj_arg child);
extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg world, b_obj_arg child);
extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg world, b_obj_arg child);
extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg world, obj_arg child);

#endif

}
