/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include <cstdio>
#include <memory>
#include <string>
#include "runtime/libuv.h"
#include "runtime/object.h"
#include "runtime/thread.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

static std::unique_ptr<lthread> g_libuv_thread;

// How long `finalize_libuv` waits for outstanding threadpool requests before abandoning them. Only
// reached when a request is stuck in an uninterruptible syscall; the common case exits immediately.
static constexpr uint64_t LEAN_UV_TEARDOWN_DRAIN_NS = 100ull * 1000ull * 1000ull;

extern "C" void initialize_libuv() {
    initialize_libuv_timer();
    initialize_libuv_tcp_socket();
    initialize_libuv_udp_socket();
    initialize_libuv_signal();
    initialize_libuv_loop();

    g_libuv_thread.reset(new lthread([]() { event_loop_run_loop(&global_ev); }));
}

// Tears the event loop down. This is terminal: `initialize_libuv` is only ever called from
// `initialize_runtime_module`, so the loop is not restarted afterwards and every subsequent uv
// operation fails with `UV_ECANCELED`. Embedders that construct more than one `scoped_task_manager`
// in a process therefore get a working loop only for the first one.
extern "C" void finalize_libuv() {
    if (g_libuv_thread == nullptr) {
        return;
    }

    event_loop_begin_teardown();

    event_loop_lock_internal(&global_ev);
    event_loop_request_stop(&global_ev);
    event_loop_unlock(&global_ev);

    g_libuv_thread->join();
    g_libuv_thread = nullptr;

    event_loop_lock_internal(&global_ev);

    uv_deferred_teardown deferred_teardown;

    uv_walk(global_ev.loop, [](uv_handle_t * handle, void * arg) {
        if (uv_is_closing(handle)) {
            return;
        }

        if (uv_handle_get_type(handle) == UV_ASYNC) {
            uv_close(handle, nullptr);
            return;
        }

        uv_deferred_teardown * deferred = (uv_deferred_teardown *)arg;
        lean_object * obj = (lean_object*)handle->data;

        if (obj != nullptr) {
            switch (uv_handle_get_type(handle)) {
                case UV_TIMER:
                    lean_uv_timer_shutdown(obj, *deferred);
                    break;
                case UV_TCP:
                    lean_uv_tcp_socket_shutdown(obj, *deferred);
                    break;
                case UV_UDP:
                    lean_uv_udp_socket_shutdown(obj, *deferred);
                    break;
                case UV_SIGNAL:
                    lean_uv_signal_shutdown(obj, *deferred);
                    break;
                default: {
                    char const * name = uv_handle_type_name(uv_handle_get_type(handle));
                    std::string msg = "libuv teardown reached an unhandled handle type: ";
                    msg += name != nullptr ? name : "unknown";
                    lean_internal_panic(msg.c_str());
                }
            }
        }

        uv_close(handle, [](uv_handle_t * handle) { free(handle); });
    }, &deferred_teardown);

    event_loop_mark_finalized(&global_ev);
    event_loop_cancel_requests(&global_ev);

    uint64_t const deadline = uv_hrtime() + LEAN_UV_TEARDOWN_DRAIN_NS;

    // The first pass runs the close callbacks the walk queued. Anything that survives it is a
    // threadpool request whose worker has to finish on its own, so the poll below is only ever
    // reached in that case and sleeping between passes costs nothing in the common one.
    while (uv_run(global_ev.loop, UV_RUN_NOWAIT) != 0) {
        if (uv_hrtime() >= deadline) {
            break;
        }

        uv_sleep(1);
    }

    bool abandoned = event_loop_abandon_requests(&global_ev);

    if (!abandoned) {
        int close_result = uv_loop_close(global_ev.loop);

        if (close_result != 0) {
            // Not worth aborting the process for: `main` has already produced its output, and the
            // only cost of an unclosed loop is that its allocations survive into a leak report.
            fprintf(stderr, "warning: libuv event loop did not close at exit: %s\n",
                    uv_strerror(close_result));
        }
    }

    deferred_teardown.run();

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
