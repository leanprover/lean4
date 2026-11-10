/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <lean/lean.h>
#include "runtime/thread.h"
#include "runtime/uv/event_loop.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

inline lean_external_class * g_uv_process_external_class = nullptr;
void initialize_libuv_process();

#ifndef LEAN_EMSCRIPTEN

// A spawned child process, the last field of an `IO.Process.Child`. Allocated with `new`; the close
// callback deletes it.
//
// The handle stays open until the child has exited, so that libuv reaps the child even when the
// `Child` is dropped before: of the finalizer and the exit callback, the one that runs second closes
// the handle. Both run under the loop lock, which guards `m_dropped`.
struct lean_uv_process_object {
    uv_process_t       m_uv_process;
    bool               m_setsid = false;     // Whether the child leads its own session and process group.
    bool               m_dropped = false;    // Whether the `Child` has been finalized.

    // The exit callback sets these under both the loop lock and `m_mutex`, so either lock suffices
    // to read them.
    mutex              m_mutex;
    condition_variable m_exited_cond;
    bool               m_exited = false;
    uint32_t           m_exit_code = 0;
};

static inline lean_object * lean_uv_process_new(lean_uv_process_object * p) { return lean_alloc_external(g_uv_process_external_class, p); }
static inline lean_uv_process_object * lean_to_uv_process(lean_object * o) { return (lean_uv_process_object *)(lean_get_external_data(o)); }

#endif

// =======================================
// Process manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_io_process_spawn(lean_obj_arg args);
extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_wait(b_lean_obj_arg cfg, b_lean_obj_arg child);
extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_try_wait(b_lean_obj_arg cfg, b_lean_obj_arg child);
extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_kill(b_lean_obj_arg cfg, b_lean_obj_arg child, uint8_t force);
extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_lean_obj_arg cfg, b_lean_obj_arg child);
extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_take_stdin(b_lean_obj_arg cfg, lean_obj_arg child);

}
