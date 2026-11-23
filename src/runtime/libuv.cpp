/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include "runtime/libuv.h"
#include <mutex>
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

extern "C" void initialize_libuv() {
    initialize_libuv_timer();
    initialize_libuv_tcp_socket();
    initialize_libuv_udp_socket();
    initialize_libuv_signal();
    initialize_libuv_process();
    global_ev.start();
}

extern "C" LEAN_EXPORT char ** lean_setup_args(int argc, char ** argv) {
    return uv_setup_args(argc, argv);
}

// Takes what a handle's pending operations hold, stopping them as their `stop` or `cancel` would.
static void take_pending(uv_handle_t * handle, void * arg) {
    // A closing handle was closed by `close` or a finalizer, which released what it held.

    if (uv_is_closing(handle) || handle == (uv_handle_t*)&global_ev.m_flush_timer) {
        return;
    }

    uv_finalize_batch & batch = *static_cast<uv_finalize_batch *>(arg);
    switch (handle->type) {
    case UV_TIMER: timer_take_pending(handle, batch); break;
    case UV_SIGNAL: signal_take_pending(handle, batch); break;
    case UV_TCP: tcp_take_pending(handle, batch); break;
    case UV_UDP: udp_take_pending(handle, batch); break;
    case UV_PROCESS: process_cancel_waits(handle); break;
    default: break;
    }
}

// The socket a request writes to, connects or shuts down, or null for thread-pool work.
static uv_handle_t * request_socket(uv_req_t * req) {
    switch (req->type) {
    case UV_WRITE: return (uv_handle_t*)((uv_write_t*)req)->handle;
    case UV_CONNECT: return (uv_handle_t*)((uv_connect_t*)req)->handle;
    default: return nullptr;
    }
}

// Takes the promises of linked requests. A request stays linked: libuv owns it until its callback
// runs, which then finds no promise and frees it.
static void take_requests(uv_finalize_batch & batch) {
    for (uv_tracked_req * req = g_uv_requests; req != nullptr; req = req->m_next) {
        bool sends = req->m_uv->type == UV_WRITE || req->m_uv->type == UV_UDP_SEND;

        if (batch.m_keep_flushable) {
            if (req->promise.get() == nullptr || sends) {
                continue;
            }
            // Keeps a queued thread-pool request (DNS, random) from starting: libuv's exit
            // destructor runs every queued one before joining its workers. A cancelled one completes
            // in the flush. Fails harmlessly for the others.
            uv_cancel(req->m_uv);
        } else if (uv_handle_t * socket = request_socket(req->m_uv)) {
            batch.m_close.push_back(socket);
        }

        if (req->promise.get() != nullptr) {
            batch.m_promises.push_back(std::move(req->promise));
        }
    }
}

// Whether a write, UDP send or TCP shutdown is still waiting for the flush.
static bool flush_pending() {
    for (uv_tracked_req * req = g_uv_requests; req != nullptr; req = req->m_next) {
        if (req->promise.get() != nullptr) {
            return true;
        }
    }

    bool shutdown = false;

    uv_walk(global_ev.m_loop, [](uv_handle_t * handle, void * arg) {
        if (handle->type == UV_TCP && !uv_is_closing(handle) && tcp_shutdown_pending(handle)) {
            *static_cast<bool*>(arg) = true;
        }
    }, &shutdown);

    return shutdown;
}

// Whether a closed socket's write or connect still waits for libuv to cancel it.
static bool socket_requests_pending() {
    for (uv_tracked_req * req = g_uv_requests; req != nullptr; req = req->m_next) {
        if (request_socket(req->m_uv) != nullptr) {
            return true;
        }
    }
    return false;
}

static void settle_cancelled(uv_finalize_batch & batch) {
    for (owned_ref & promise : batch.m_promises) {
        lean_promise_resolve(mk_except_err(lean_decode_uv_error(UV_ECANCELED, nullptr)), promise.get());
    }
}

// How long finalization waits for pending writes before cancelling them.
static constexpr uint64_t g_uv_flush_timeout_ms = 2000;
// How long it then waits for libuv to cancel the requests of the sockets it closed. On Unix that
// takes one loop iteration.
static constexpr uint64_t g_uv_close_timeout_ms = 500;

// `IO.Process.exit` and the task manager's finalization may stop libuv at the same time. Recursive,
// since a `(sync := true)` continuation run by the settle may call `IO.Process.exit`, which stops
// libuv again on the same thread.
static std::recursive_mutex g_uv_stop_mutex;

extern "C" LEAN_EXPORT void lean_uv_stop() {
    // The loop thread cannot join itself, so the loop keeps running. Checked before taking the
    // mutex, since a thread holding it may be joining the loop thread.
    if (global_ev.on_loop_thread()) {
        global_ev.stop();
        return;
    }
    std::lock_guard<std::recursive_mutex> stopping(g_uv_stop_mutex);
    if (!global_ev.stop()) {
        return;
    }

    // Everything is settled at the end: continuations run on the pool, and one that closes a socket
    // during the flush would cancel the writes being flushed.
    uv_finalize_batch batch;

    // Waits (timers, signals, reads, accepts, child waits) and work that sends nothing (connects,
    // DNS, random) are cancelled first.
    batch.m_keep_flushable = true;

    {
        event_loop_guard guard;
        if (guard.exiting()) {
            return;
        }
        uv_walk(global_ev.m_loop, take_pending, &batch);
        take_requests(batch);
    }

    // Writes and shutdowns get to finish, but a peer that does not read must not hold up the exit.
    global_ev.flush(g_uv_flush_timeout_ms, flush_pending);

    // Then everything still in flight is cancelled, and the sockets it uses are closed, so that a
    // restarted loop does not send what the program was told was cancelled.
    batch.m_keep_flushable = false;

    {
        event_loop_guard guard;
        if (guard.exiting()) {
            return;
        }
        uv_walk(global_ev.m_loop, take_pending, &batch);
        take_requests(batch);
        for (uv_handle_t * socket : batch.m_close) {
            if (!uv_is_closing(socket)) {
                tcp_close_for_finalization(socket);
            }
        }
    }

    global_ev.flush(g_uv_close_timeout_ms, socket_requests_pending);

    settle_cancelled(batch);
}

// Whether a closed handle still waits for its close callback.
static bool handles_closing() {
    bool closing = false;
    uv_walk(global_ev.m_loop, [](uv_handle_t * handle, void * arg) {
        if (uv_is_closing(handle)) {
            *static_cast<bool*>(arg) = true;
        }
    }, &closing);
    return closing;
}

// How long the last pass waits for close callbacks. On Unix that takes one loop iteration.
static constexpr uint64_t g_uv_free_timeout_ms = 500;

extern "C" LEAN_EXPORT void lean_uv_free_closed() {
    // The loop thread still runs when the stop happened on it.
    if (!global_ev.joined()) {
        return;
    }
    // Finalizers that ran after the stop closed their handles, but only a loop iteration runs the
    // close callbacks that free them. No callback resolves a promise any more, since the stop took
    // them all, so this is safe without a task manager.
    global_ev.flush(g_uv_free_timeout_ms, handles_closing);
}

/* Std.Internal.UV.Loop.canceledCode : Unit → UInt32 */
extern "C" LEAN_EXPORT uint32_t lean_uv_canceled_code(lean_obj_arg) {
    return static_cast<uint32_t>(-UV_ECANCELED);
}

extern "C" LEAN_EXPORT void lean_uv_restart() {
    global_ev.restart();
}

/* Lean.libUVVersionFn : Unit → Nat */
extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

#else

extern "C" void initialize_libuv() {}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT char ** lean_setup_args(int argc, char ** argv) {
    return argv;
}

extern "C" LEAN_EXPORT void lean_uv_stop() {}

extern "C" LEAN_EXPORT void lean_uv_free_closed() {}

extern "C" LEAN_EXPORT uint32_t lean_uv_canceled_code(lean_obj_arg) {
    return 0;
}
extern "C" LEAN_EXPORT void lean_uv_restart() {}


#endif
}
