/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include "runtime/libuv.h"
#include <mutex>
#include <vector>
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
// Handle constructors set `data` under the loop lock, since this reads it as the owning object.
static void take_pending(uv_handle_t * handle, void * arg) {
    // A closing handle was closed by `close` or a finalizer, which released what it held. A signal
    // handle without `data` lost its object after the stop and only keeps listening.
    if (uv_is_closing(handle) || handle->data == nullptr || handle == (uv_handle_t*)&global_ev.m_flush_timer) {
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
            // destructor runs every queued one before joining its workers. Its callback, which
            // frees it, runs whenever the loop next runs. Fails harmlessly for the others.
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

static void settle_cancelled(uv_finalize_batch & batch) {
    for (owned_ref & promise : batch.m_promises) {
        lean_promise_resolve(mk_except_err(lean_decode_uv_error(UV_ECANCELED, nullptr)), promise.get());
    }
}

// How long finalization waits for pending writes before cancelling them.
static constexpr uint64_t g_uv_flush_timeout_ms = 2000;

// `IO.Process.exit` and the task manager's finalization may stop libuv at the same time. Never
// destroyed, since `exit()` runs static destructors while another thread may hold it.
static std::mutex & g_uv_stop_mutex = *new std::mutex;

// For `IO.Process.exit`, which runs `exit()` right after: nothing could observe the settled
// promises, and dropping one would run its `(sync := true)` continuations, such as `result!`, inline.
static void leak(uv_finalize_batch & batch) {
    for (owned_ref & promise : batch.m_promises) {
        (void)promise.release();
    }
    for (owned_ref & ref : batch.m_refs) {
        (void)ref.release();
    }
}

static void stop_libuv(bool settle) {
    // The loop thread cannot join itself, so the loop keeps running. Checked before taking the
    // mutex, since a thread holding it may be joining the loop thread.
    if (global_ev.on_loop_thread()) {
        global_ev.stop();
        return;
    }
    std::unique_lock<std::mutex> stopping(g_uv_stop_mutex);
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
            leak(batch);
            return;
        }
        uv_walk(global_ev.m_loop, take_pending, &batch);
        take_requests(batch);
    }

    // Writes and shutdowns get to finish, but a peer that does not read must not hold up the exit.
    global_ev.flush(g_uv_flush_timeout_ms, flush_pending);

    // Then everything still in flight is cancelled, and the TCP sockets it uses are closed, so that a
    // restarted loop does not send what the program was told was cancelled. libuv completes their
    // requests with `UV_ECANCELED` when the loop next runs, at the latest in `lean_uv_free_closed`.
    batch.m_keep_flushable = false;

    {
        event_loop_guard guard;
        if (guard.exiting()) {
            leak(batch);
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

    if (!settle) {
        leak(batch);
        return;
    }
    // Continuations run by the settle may call `IO.Process.exit`, which stops libuv again.
    stopping.unlock();
    settle_cancelled(batch);
}

extern "C" LEAN_EXPORT void lean_uv_stop() {
    stop_libuv(true);
}

extern "C" LEAN_EXPORT void lean_uv_stop_for_exit() {
    // Pending writes get the same bounded flush as when `main` returns.
    stop_libuv(false);
    global_ev.stop_for_exit();
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

// How long the last pass waits for close callbacks, and the cancelled requests' callbacks that run
// before them. On Unix that takes one loop iteration.
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

/* IO.Error.canceledCode : Unit → UInt32 */
extern "C" LEAN_EXPORT uint32_t lean_uv_canceled_code(lean_obj_arg) {
    return static_cast<uint32_t>(-UV_ECANCELED);
}

// Before a restart: handles left from the last finalization that would otherwise outlive it.
static void restart_handle(uv_handle_t * handle, void *) {
    if (uv_is_closing(handle)) {
        return;
    }
    if (handle->type == UV_SIGNAL && handle->data == nullptr) {
        signal_close_orphan(handle);
    } else if (handle->type == UV_PROCESS) {
        process_restart(handle);
    }
}

extern "C" LEAN_EXPORT void lean_uv_restart() {
    if (global_ev.m_loop != nullptr && !global_ev.exiting()) {
        event_loop_guard guard;
        uv_walk(global_ev.m_loop, restart_handle, nullptr);
    }
    global_ev.restart();
}

// Promises that stay pending until the program ends: dropping one would make `result!` on it block.
/* Std.Internal.UV.Signal.keepPending (promise : @& IO.Promise Int) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_keep_pending(b_obj_arg promise) {
    static std::mutex & mutex = *new std::mutex;
    static std::vector<lean_object *> & kept = *new std::vector<lean_object *>;
    lean_inc(promise);
    std::lock_guard<std::mutex> lock(mutex);
    kept.push_back(promise);
    return lean_box(0);
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

// Without libuv nothing is canceled, so this matches no error code.
extern "C" LEAN_EXPORT uint32_t lean_uv_canceled_code(lean_obj_arg) {
    return UINT32_MAX;
}
extern "C" LEAN_EXPORT void lean_uv_restart() {}

extern "C" LEAN_EXPORT void lean_uv_stop_for_exit() {}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_keep_pending(b_obj_arg) {
    return lean_box(0);
}


#endif
}
