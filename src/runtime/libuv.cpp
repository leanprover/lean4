/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include <pthread.h>
#include "runtime/libuv.h"
#include "runtime/object.h"

#include <memory>

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

static std::unique_ptr<lthread> g_libuv_thread;

extern "C" void initialize_libuv() {
    initialize_libuv_timer();
    initialize_libuv_tcp_socket();
    initialize_libuv_udp_socket();
    initialize_libuv_signal();
    initialize_libuv_loop();

    g_libuv_thread.reset(new lthread([]() { event_loop_run_loop(&global_ev); }));
}

// Stops the event loop thread. `lean_finalize_task_manager` calls this once the workers have
// finished and before it frees the task manager, which the loop thread resolves promises through.
// Joining the loop thread waits for a callback it is running, including a `(sync := true)`
// continuation, so one that blocks delays the exit for as long as it blocks.
//
// The loop is only left, not torn down: its handles, its requests and the promises they hold stay
// reachable from it, still pending, and no callback runs again. Threadpool requests that have not
// started are cancelled so that libuv's threadpool shutdown at exit does not run them first. The
// loop thread is not restarted, so an embedder that creates another task manager gets uv operations
// that never complete.
extern "C" void finalize_libuv() {
    if (g_libuv_thread == nullptr) {
        return;
    }

    event_loop_lock(&global_ev);
    event_loop_request_stop(&global_ev);
    event_loop_unlock(&global_ev);

    g_libuv_thread->join();
    g_libuv_thread = nullptr;

    event_loop_lock(&global_ev);
    event_loop_cancel_requests(&global_ev);
    event_loop_unlock(&global_ev);
}

extern "C" LEAN_EXPORT char ** lean_setup_args(int argc, char ** argv) {
    return uv_setup_args(argc, argv);
}

/* Lean.libUVVersionFn : Unit → Nat */
extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

#else

extern "C" void initialize_libuv() {}
extern "C" void finalize_libuv() {}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT char ** lean_setup_args(int argc, char ** argv) {
    return argv;
}


#endif
}
