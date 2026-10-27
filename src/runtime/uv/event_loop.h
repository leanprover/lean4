/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/uv/util.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#include <atomic>
#include <vector>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

class event_loop_guard;
class lthread;

// The libuv loop, shared by all threads. libuv is not thread-safe, so the loop thread and every other
// thread take turns holding `m_mutex`, and every libuv call and handle field is accessed under it:
//
// - The loop thread holds it while it runs `uv_run`, so callbacks run with it held.
//
// - A thread that finds it taken counts itself in `m_waiters` and then sends on `m_async`, which makes
//   `uv_run` return. Counting first means the loop thread sees the waiter when it takes the mutex again,
//   and waits on `m_cond` instead of starting another iteration.
//
// - `unlock` signals `m_cond` only when no waiter is left. The last unlock always sees zero, so the loop
//   thread is never left waiting.
//
// - The mutex is recursive, since callbacks call back into the bindings. The loop thread waits on
//   `m_cond` only between iterations, at depth 1, where waiting fully releases the mutex.
//
// When the task manager shuts down, `stop` ends the loop thread and tears the loop down: it closes every
// handle and runs the loop until everything has finished. No Lean code runs during the teardown.
// Everything the loop held is released once the loop is closed, including promises that are still
// pending: no worker is left by then, so the task manager discards their continuations, `(sync := true)`
// ones included. When the task manager restarts, `start` starts a fresh loop, and a handle the teardown
// closed stays closed.
class event_loop {
public:
    uv_loop_t * m_loop = nullptr;

    // Starts a fresh loop and the loop thread, at startup and again after each `stop`.
    void start();

    // Tears the loop down. Called after the task manager's workers have finished.
    void stop();

    // Whether the loop has work other than `m_async`.
    bool alive(event_loop_guard const &);

    // Whether the loop is still running, as opposed to torn down by `stop`. Call with the lock held.
    bool running() const { return m_running; }

    // Hands a reference to the loop during the teardown. Call with the lock held.
    void exit_drop(owned_ref ref);

private:
    uv_loop_t        m_loop_storage;
    uv_mutex_t       m_mutex;
    uv_cond_t        m_cond;
    uv_async_t       m_async;   // Interrupts `uv_run` for a waiting thread.
    std::atomic<int> m_waiters; // Threads waiting for `m_mutex`.
    // Orders every send on `m_async` before `stop` closes it.
    uv_mutex_t       m_async_mutex;
    bool             m_running = false;
    lthread *        m_thread = nullptr;
    // What the teardown releases once the loop is closed.
    std::vector<owned_ref> m_released;

    void lock();
    void unlock();
    void run();

    friend class event_loop_guard;
};

extern event_loop global_ev;

// Holds the `global_ev` lock for its scope. Must be a named local: a temporary would unlock
// immediately. libuv callbacks already run under the lock and do not take it, but a finalizer or an FFI
// call from a continuation they run inline does; the lock is recursive, so this nests.
class event_loop_guard {
public:
    [[nodiscard]] event_loop_guard() { global_ev.lock(); }
    ~event_loop_guard() { global_ev.unlock(); }
    event_loop_guard(event_loop_guard const &) = delete;
    event_loop_guard & operator=(event_loop_guard const &) = delete;

    // Whether the loop is torn down, between a `stop` and the next `start`. An FFI entry point then fails
    // with `UV_ECANCELED` instead of calling libuv.
    bool stopped() const { return !global_ev.running(); }

    // Whether `handle` can no longer be used: the loop is torn down, or a teardown closed the handle before
    // the loop was started again. A finalizer closes only handles that Lean code can no longer reach.
    template<class H>
    bool closed(H * handle) const { return stopped() || uv_is_closing((uv_handle_t*)handle); }
};

// The first thing a request callback does: during the teardown at exit it hands the request's
// references to the loop and returns `true`, so the callback must not resolve anything.
template<class... Refs>
bool uv_dropped_at_exit(Refs &... refs) {
    if (global_ev.running()) {
        return false;
    }
    (global_ev.exit_drop(std::move(refs)), ...);
    return true;
}

#endif

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options);
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive();

}
