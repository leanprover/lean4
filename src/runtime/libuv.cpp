/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include "runtime/libuv.h"
#include <chrono>
#include <mutex>
#include <string>
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
    // A closing handle was closed by `close` or a finalizer, which released what it held.
    if (uv_is_closing(handle) || global_ev.is_own_handle(handle)) return;

    // Its pending operations could not be stopped.
    if (handle->data == nullptr) {
        lean_internal_panic((std::string("libuv finalization found a ") + uv_handle_type_name(handle->type) + " handle without its object").c_str());
    }

    uv_finalize_batch & batch = *static_cast<uv_finalize_batch *>(arg);
    lean_object * obj = static_cast<lean_object *>(handle->data);

    switch (handle->type) {
    case UV_TIMER: timer_take_pending(obj, batch); break;
    case UV_SIGNAL: signal_take_pending(obj, batch); break;
    case UV_TCP: tcp_take_pending(obj, batch); break;
    case UV_UDP: udp_take_pending(obj, batch); break;

    // A woken `Child.wait` runs its caller at once, which must not close a socket during the flush.
    case UV_PROCESS: if (!batch.m_keep_flushable) process_set_cancelled(handle, true); break;

    default: lean_internal_panic((std::string("libuv finalization does not handle ") + uv_handle_type_name(handle->type) + " handles").c_str());
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
static std::timed_mutex & g_uv_stop_mutex = *new std::timed_mutex;

// How long `IO.Process.exit` waits for each lock before it gives up on stopping libuv: a `(sync := true)`
// continuation that blocks, for example on a mutex the exiting thread holds, keeps the loop's lock, and
// one run by a flush keeps `g_uv_stop_mutex`. Longer than a flush, which holds `g_uv_stop_mutex`
// throughout.
static event_loop::deadline exit_lock_deadline(uint64_t flush_timeout_ms) {
    return std::chrono::steady_clock::now() + std::chrono::milliseconds(flush_timeout_ms + 1000);
}

// Returns false if `IO.Process.exit` (`!settle`) timed out waiting for a lock. Waits without bound when
// `main` returns, since the task manager's finalization waits for blocked tasks anyway.
static bool stop_libuv(bool settle, uint64_t flush_timeout_ms) {
    auto deadline = [&] {
        return settle ? event_loop::no_deadline : exit_lock_deadline(flush_timeout_ms);
    };
    // The loop thread cannot join itself, so the loop keeps running. Checked before taking the
    // mutex, since a thread holding it may be joining the loop thread.
    if (global_ev.on_loop_thread()) {
        global_ev.stop();
        if (!settle) {
            // `exit()` follows without the passes.
            event_loop_guard guard;
            if (!guard.exiting()) cancel_queued_work();
        }
        return true;
    }
    std::unique_lock<std::timed_mutex> stopping(g_uv_stop_mutex, std::defer_lock);

    if (settle) {
        stopping.lock();
    } else if (!stopping.try_lock_until(deadline())) {
        return false;
    }

    switch (global_ev.stop(deadline())) {
    case event_loop::stop_result::timed_out: return false;
    case event_loop::stop_result::not_joined: return true;
    case event_loop::stop_result::joined: break;
    }

    // What the passes take is settled only after the flush, since a continuation that closes a socket
    // during it would cut short the writes being flushed. Writes and shutdowns that finish during the
    // flush settle their own promises then.
    uv_finalize_batch batch;

    // Waits (timers, signals, reads, accepts) and work that sends nothing (connects, DNS, random) are
    // cancelled first; child waits only after the flush.
    batch.m_keep_flushable = true;
    if (!take_all(batch)) return true;

    // Writes and shutdowns get to finish, but a peer that does not read must not hold up the exit.
    global_ev.flush(flush_timeout_ms, flush_pending);

    // Then everything still in flight is cancelled, and the TCP sockets it uses are closed, so that a
    // restarted loop does not send what the program was told was cancelled. libuv completes their
    // requests with `UV_ECANCELED` when the loop next runs, at the latest in `lean_uv_free_closed`.
    // A UDP send still queued is only settled: libuv cannot cancel it without closing the socket,
    // so its datagram may still go out.
    batch.m_keep_flushable = false;
    if (!take_all(batch)) return true;

    if (!settle) {
        keep_until_exit(batch);
        return true;
    }
    // Continuations run by the settle may call `IO.Process.exit`, which stops libuv again.
    stopping.unlock();
    for (owned_ref & promise : batch.m_promises) {
        lean_promise_resolve(mk_except_err(lean_decode_uv_error(UV_ECANCELED, nullptr)), promise.get());
    }

    return true;
}

extern "C" LEAN_EXPORT void lean_uv_stop() {
    stop_libuv(true, g_uv_flush_timeout_ms);
}

extern "C" LEAN_EXPORT bool lean_uv_stop_for_exit(uint32_t grace_period_ms) {
    return stop_libuv(false, grace_period_ms)
        && global_ev.stop_for_exit(exit_lock_deadline(grace_period_ms));
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
    std::lock_guard<std::timed_mutex> stopping(g_uv_stop_mutex);
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
        // Children that the last finalization cancelled can be waited for again.
        uv_walk(global_ev.m_loop, [](uv_handle_t * handle, void *) {
            if (!uv_is_closing(handle) && handle->type == UV_PROCESS) {
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
extern "C" LEAN_EXPORT bool lean_uv_stop_for_exit(uint32_t) { return true; }
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
