/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#include <atomic>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

class event_loop_guard;

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
class event_loop {
public:
    uv_loop_t * m_loop;

    // Initializes the loop and starts the loop thread.
    void start();

    // Whether the loop has work other than `m_async`.
    bool alive(event_loop_guard const &);

    // Whether the caller is the loop thread, which runs every callback and the continuations that
    // these run inline. No callback runs while that thread is blocked.
    bool on_loop_thread() const;

    // Whether the program is finishing: operations fail with `UV_ECANCELED` instead of starting new
    // libuv work. The loop keeps running, so pending operations still complete, and cancellations,
    // closes and finalizers still clean up.
    bool stopped() const { return m_stopped.load(std::memory_order_acquire); }

    // Whether `IO.Process.exit` holds the lock for good. Then no thread may touch libuv at all.
    bool exiting() const { return m_exiting.load(std::memory_order_acquire); }

    // Set by `lean_finalize_task_manager` before it waits for running tasks, and cleared by
    // `lean_init_task_manager`.
    void stop();
    void restart();

    // Stops libuv for `IO.Process.exit`, which then runs `exit()` while other threads keep running.
    // Takes the lock and never releases it: a thread already past the `exiting` check waits on it
    // forever, so no thread is inside libuv when `exit()` runs libuv's destructor, and the loop thread
    // runs no more callbacks.
    void stop_for_exit();

private:
    uv_mutex_t       m_mutex;
    uv_cond_t        m_cond;
    uv_async_t       m_async;   // Interrupts `uv_run` for a waiting thread.
    std::atomic<int> m_waiters; // Threads waiting for `m_mutex`.
    std::atomic<bool> m_stopped{false};
    std::atomic<bool> m_exiting{false};

    void lock();
    void unlock();
    void run();

    friend class event_loop_guard;
};

extern event_loop global_ev;

// Holds the `global_ev` lock for its scope. Must be a named local: a temporary would unlock
// immediately. libuv callbacks already run under the lock and do not take it, but a finalizer or an FFI
// call from a continuation they run inline does; the lock is recursive, so this nests.
//
// An operation checks `stopped()` and then fails with `UV_ECANCELED`; it is checked after locking,
// since libuv may stop while this thread waits for the lock. While `IO.Process.exit` runs the guard
// does not lock at all, so a cancellation, close or finalizer checks `exiting()` and then does nothing.
class event_loop_guard {
    bool m_locked;
public:
    [[nodiscard]] event_loop_guard() : m_locked(!global_ev.exiting()) {
        if (m_locked) global_ev.lock();
    }
    ~event_loop_guard() { if (m_locked) global_ev.unlock(); }
    event_loop_guard(event_loop_guard const &) = delete;
    event_loop_guard & operator=(event_loop_guard const &) = delete;

    bool stopped() const { return !m_locked || global_ev.stopped(); }
    bool exiting() const { return !m_locked; }
};

#endif

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive();
extern "C" LEAN_EXPORT void lean_uv_stop_for_exit();
extern "C" LEAN_EXPORT void lean_uv_stop();
extern "C" LEAN_EXPORT void lean_uv_restart();

}
