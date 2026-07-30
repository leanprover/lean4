/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include <memory>
#include <utility>
#include <vector>
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
#define LEAN_UV_TEARDOWN_DRAIN_NS (100ull * 1000ull * 1000ull)

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

    // Must precede any `lean_dec` below that could reach a handle finalizer: those run on this
    // thread and rely on being recognised so they do not wait for a state we have not reached yet.
    event_loop_begin_teardown(&global_ev);

    event_loop_lock_internal(&global_ev);
    event_loop_request_stop(&global_ev);
    event_loop_unlock(&global_ev);

    g_libuv_thread->join();
    g_libuv_thread = nullptr;

    event_loop_drain_active(&global_ev);
    event_loop_lock_internal(&global_ev);

    uv_deferred_releases pending_releases;

    uv_walk(global_ev.loop, [](uv_handle_t * handle, void * arg) {
        if (uv_is_closing(handle)) {
            return;
        }

        if (uv_handle_get_type(handle) == UV_ASYNC) {
            uv_close(handle, nullptr);
            return;
        }

        uv_deferred_releases * deferred = (uv_deferred_releases *)arg;
        lean_object * obj = (lean_object*)handle->data;

        if (obj != nullptr) {
            size_t releases = 0;

            switch (uv_handle_get_type(handle)) {
                case UV_TIMER:
                    releases = lean_uv_timer_shutdown(lean_to_uv_timer(obj));
                    break;
                case UV_TCP:
                    releases = lean_uv_tcp_socket_shutdown(lean_to_uv_tcp_socket(obj), *deferred);
                    break;
                case UV_UDP:
                    releases = lean_uv_udp_socket_shutdown(lean_to_uv_udp_socket(obj));
                    break;
                case UV_SIGNAL:
                    releases = lean_uv_signal_shutdown(lean_to_uv_signal(obj));
                    break;
                default:
                    lean_assert(false);
                    return;
            }

            if (releases > 0) {
                deferred->emplace_back(obj, releases);
            }
        }

        uv_close(handle, [](uv_handle_t * handle) { free(handle); });
    }, &pending_releases);

    // Mark the loop finalized before draining it. The walk above detached every wrapper's handle and
    // requested its close, which makes libuv cancel in-flight stream requests (connect/send/shutdown)
    // and fire their callbacks during the `uv_run` below. Those callbacks may drop the last reference
    // to a socket; marking finalized first ensures the resulting finalizer sees the loop gone and
    // frees its already-detached wrapper immediately instead of blocking in
    // `event_loop_wait_finalized`. We still hold the mutex, so finalizers on other threads waiting in
    // `event_loop_wait_finalized` stay blocked until teardown fully completes.
    event_loop_mark_finalized(&global_ev);

    // Requests bound to the loop rather than to a handle (DNS, `uv_random`) are invisible to the
    // walk above, so cancel them explicitly. Whatever is still queued completes promptly during the
    // drain; whatever already reached a threadpool worker cannot be interrupted at all.
    event_loop_cancel_requests(&global_ev);

    // Drain with `UV_RUN_NOWAIT` rather than `UV_RUN_DEFAULT`. The close callbacks queued by the
    // walk, and the connect/send/shutdown callbacks libuv cancels along with them, all complete in
    // a bounded number of iterations. `UV_RUN_DEFAULT` would additionally block until every
    // threadpool request finished, which an unresponsive resolver can delay indefinitely.
    uint64_t const deadline = uv_hrtime() + LEAN_UV_TEARDOWN_DRAIN_NS;

    while (uv_run(global_ev.loop, UV_RUN_NOWAIT) != 0) {
        if (uv_hrtime() >= deadline) {
            break;
        }

        // Only an outstanding threadpool request can keep the loop alive for long; yield to it
        // instead of spinning. Handle work needs no wait and falls out of the loop immediately.
        if (event_loop_has_requests(&global_ev)) {
            uv_sleep(1);
        }
    }

    size_t abandoned = event_loop_detach_requests(&global_ev);

    // With requests abandoned the loop still owns them, so `uv_loop_close` would return `UV_EBUSY`.
    // Leaving the loop open at process exit is harmless; it is a static.
    if (abandoned == 0) {
        int close_result = uv_loop_close(global_ev.loop);
        lean_always_assert(close_result == 0);
    }

    // Release the references the loop held on the surviving wrappers. Deferred until now because
    // these `lean_dec`s can run wrapper finalizers, which must observe the finalized loop.
    for (auto & release : pending_releases) {
        for (size_t i = 0; i < release.second; i++) {
            lean_dec(release.first);
        }
    }

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
