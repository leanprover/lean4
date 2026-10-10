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

private:
    uv_mutex_t       m_mutex;
    uv_cond_t        m_cond;
    uv_async_t       m_async;   // Interrupts `uv_run` for a waiting thread.
    std::atomic<int> m_waiters; // Threads waiting for `m_mutex`.

    void lock();
    void unlock();
    void run();

    friend class event_loop_guard;
};

extern event_loop global_ev;

// Holds the `global_ev` lock for its scope. Must be a named local: a temporary would unlock
// immediately. Not for libuv callbacks, which already run under the lock.
class event_loop_guard {
public:
    [[nodiscard]] event_loop_guard() { global_ev.lock(); }
    ~event_loop_guard() { global_ev.unlock(); }
    event_loop_guard(event_loop_guard const &) = delete;
    event_loop_guard & operator=(event_loop_guard const &) = delete;
};

#endif

// =======================================
// Global event loop manipulation functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options);
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive();

}
