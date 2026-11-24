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
    lean_object * obj = static_cast<lean_object *>(handle->data);
    switch (handle->type) {
    case UV_TIMER: timer_take_pending(obj, batch); break;
    case UV_SIGNAL: signal_take_pending(obj, batch); break;
    case UV_TCP: tcp_take_pending(obj, batch); break;
    case UV_UDP: udp_take_pending(obj, batch); break;
    case UV_PROCESS: process_set_cancelled(handle, true); break;
    default: break;
    }
}

// For `IO.Process.exit`, which runs `exit()` right after: nothing could observe the settled
// promises, and dropping one would run its `(sync := true)` continuations, such as `result!`, inline.
// Kept reachable until the program ends, so that leak checkers do not report what it holds. Called
// with `g_uv_stop_mutex` held.
static void keep_until_exit(uv_finalize_batch & batch) {
    static std::vector<uv_finalize_batch> & kept = *new std::vector<uv_finalize_batch>;
    kept.push_back(std::move(batch));
}

// Keeps queued thread-pool requests (DNS, random) from starting: libuv's exit destructor runs every
// queued one before joining its workers. Called under the loop lock.
static void cancel_queued_work() {
    for (uv_tracked_req * req = g_uv_requests; req != nullptr; req = req->m_next) {
        uv_req_type type = req->m_uv->type;
        if (type == UV_GETADDRINFO || type == UV_GETNAMEINFO || type == UV_RANDOM) {
            uv_cancel(req->m_uv);
        }
    }
}

// Takes from handles and linked requests, and closes the sockets in `m_close`. Returns false, keeping
// the batch, if `IO.Process.exit` has stopped libuv meanwhile.
static bool take_all(uv_finalize_batch & batch) {
    event_loop_guard guard;
    if (guard.exiting()) {
        keep_until_exit(batch);
        return false;
    }
    uv_walk(global_ev.m_loop, take_pending, &batch);
    if (batch.m_keep_flushable) {
        cancel_queued_work();
    }
    for (uv_tracked_req * req = g_uv_requests; req != nullptr; req = req->m_next) {
        uv_req_type type = req->m_uv->type;
        if (batch.m_keep_flushable) {
            if (type == UV_WRITE || type == UV_UDP_SEND) continue;
        } else if (type == UV_WRITE) {
            batch.m_close.push_back((uv_handle_t*)((uv_write_t*)req->m_uv)->handle);
        } else if (type == UV_CONNECT) {
            batch.m_close.push_back((uv_handle_t*)((uv_connect_t*)req->m_uv)->handle);
        }
        if (req->promise.get() != nullptr) batch.m_promises.push_back(std::move(req->promise));
    }
    for (uv_handle_t * socket : batch.m_close) {
        if (!uv_is_closing(socket)) lean_dec(lean_uv_tcp_close((lean_object*)socket->data));
    }
    return true;
}

// Whether a write, UDP send or TCP shutdown is still waiting for the flush.
static bool flush_pending() {
    for (uv_tracked_req * req = g_uv_requests; req != nullptr; req = req->m_next) {
        if (req->promise.get() != nullptr) return true;
    }
    bool shutdown = false;
    uv_walk(global_ev.m_loop, [](uv_handle_t * handle, void * arg) {
        *static_cast<bool*>(arg) |= handle->type == UV_TCP && !uv_is_closing(handle)
            && lean_to_uv_tcp_socket((lean_object*)handle->data)->m_promise_shutdown.get() != nullptr;
    }, &shutdown);
    return shutdown;
}

// How long finalization waits for pending writes before cancelling them.
static constexpr uint64_t g_uv_flush_timeout_ms = 2000;

// `IO.Process.exit` and the task manager's finalization may stop libuv at the same time. Never
// destroyed, since `exit()` runs static destructors while another thread may hold it.
static std::mutex & g_uv_stop_mutex = *new std::mutex;

static void stop_libuv(bool settle) {
    // The loop thread cannot join itself, so the loop keeps running. Checked before taking the
    // mutex, since a thread holding it may be joining the loop thread.
    if (global_ev.on_loop_thread()) {
        global_ev.stop();
        if (!settle) {
            // `exit()` follows without the passes.
            event_loop_guard guard;
            if (!guard.exiting()) cancel_queued_work();
        }
        return;
    }
    std::unique_lock<std::mutex> stopping(g_uv_stop_mutex);
    if (!global_ev.stop()) {
        return;
    }

    // What the passes take is settled only after the flush, since a continuation that closes a socket
    // during it would cut short the writes being flushed. Writes and shutdowns that finish during the
    // flush settle their own promises then.
    uv_finalize_batch batch;

    // Waits (timers, signals, reads, accepts, child waits) and work that sends nothing (connects,
    // DNS, random) are cancelled first.
    batch.m_keep_flushable = true;
    if (!take_all(batch)) return;

    // Writes and shutdowns get to finish, but a peer that does not read must not hold up the exit.
    global_ev.flush(g_uv_flush_timeout_ms, flush_pending);

    // Then everything still in flight is cancelled, and the TCP sockets it uses are closed, so that a
    // restarted loop does not send what the program was told was cancelled. libuv completes their
    // requests with `UV_ECANCELED` when the loop next runs, at the latest in `lean_uv_free_closed`.
    // A UDP send still queued is only settled: libuv cannot cancel it without closing the socket,
    // so its datagram may still go out.
    batch.m_keep_flushable = false;
    if (!take_all(batch)) return;

    if (!settle) {
        keep_until_exit(batch);
        return;
    }
    // Continuations run by the settle may call `IO.Process.exit`, which stops libuv again.
    stopping.unlock();
    for (owned_ref & promise : batch.m_promises) {
        lean_promise_resolve(mk_except_err(lean_decode_uv_error(UV_ECANCELED, nullptr)), promise.get());
    }
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
        *static_cast<bool*>(arg) |= uv_is_closing(handle) != 0;
    }, &closing);
    return closing;
}

// How long the last pass waits for close callbacks, and the cancelled requests' callbacks that run
// before them. On Unix that takes one loop iteration.
static constexpr uint64_t g_uv_free_timeout_ms = 500;

extern "C" LEAN_EXPORT void lean_uv_free_closed() {
    // No callback resolves a promise any more, since the stop took them all, so this is safe without
    // a task manager.
    if (global_ev.on_loop_thread()) {
        return;
    }
    // A flush by `IO.Process.exit` on another thread would share the deadline timer.
    std::lock_guard<std::mutex> stopping(g_uv_stop_mutex);
    global_ev.flush(g_uv_free_timeout_ms, handles_closing);
}

/* IO.Error.canceledCode : Unit → UInt32 */
extern "C" LEAN_EXPORT uint32_t lean_uv_canceled_code(lean_obj_arg) {
    return static_cast<uint32_t>(-UV_ECANCELED);
}

extern "C" LEAN_EXPORT void lean_uv_restart() {
    if (global_ev.m_loop != nullptr) {
        event_loop_guard guard;
        if (guard.exiting()) return;
        // Handles left from the last finalization that would otherwise outlive it.
        uv_walk(global_ev.m_loop, [](uv_handle_t * handle, void *) {
            if (uv_is_closing(handle)) return;
            if (handle->type == UV_SIGNAL && handle->data == nullptr) {
                signal_close_orphan(handle);
            } else if (handle->type == UV_PROCESS) {
                process_set_cancelled(handle, false);
            }
        }, nullptr);
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
extern "C" LEAN_EXPORT void lean_uv_stop_for_exit() {}
extern "C" LEAN_EXPORT void lean_uv_free_closed() {}
extern "C" LEAN_EXPORT void lean_uv_restart() {}

// Without libuv nothing is canceled, so this matches no error code.
extern "C" LEAN_EXPORT uint32_t lean_uv_canceled_code(lean_obj_arg) {
    return UINT32_MAX;
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_keep_pending(b_obj_arg) {
    return lean_box(0);
}


#endif
}
