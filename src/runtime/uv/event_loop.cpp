/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/event_loop.h"
#include "runtime/thread.h"

namespace lean {
#ifndef LEAN_EMSCRIPTEN
event_loop global_ev;

LEAN_THREAD_VALUE(bool, g_on_loop_thread, false);

// Utility function for error checking. This function is only used inside the
// initializition of the event loop.
static void check_uv(int result, const char * msg) {
    if (result != 0) {
        std::string err_message = std::string(msg) + ": " + uv_strerror(result);
        lean_internal_panic(err_message.c_str());
    }
}

void event_loop::start() {
    // Not `uv_default_loop()`: finalization takes every handle on the loop to be a Lean object.
    m_loop = new uv_loop_t;
    check_uv(uv_loop_init(m_loop), "Failed to initialize the event loop");
    check_uv(uv_mutex_init_recursive(&m_mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&m_cond), "Failed to initialize condition variable");
    check_uv(uv_async_init(m_loop, &m_async, nullptr), "Failed to initialize async");
    check_uv(uv_timer_init(m_loop, &m_flush_timer), "Failed to initialize the flush timer");
    uv_unref((uv_handle_t*)&m_flush_timer);
    m_waiters = 0;

    m_thread = new lthread([this]() { run(); });
}

void event_loop::lock() {
    if (uv_mutex_trylock(&m_mutex) != 0) {
        m_waiters++;
        int result = uv_async_send(&m_async);
        (void)result;
        lean_assert(result == 0);
        uv_mutex_lock(&m_mutex);
        m_waiters--;
    }
}

void event_loop::unlock() {
    if (m_waiters == 0) {
        uv_cond_signal(&m_cond);
    }
    uv_mutex_unlock(&m_mutex);
}

bool event_loop::alive(event_loop_guard const &) {
    // `m_async` only wakes the loop for waiting threads and is always active, so it is left out.
    uv_unref((uv_handle_t*)&m_async);
    bool alive = uv_loop_alive(m_loop);
    uv_ref((uv_handle_t*)&m_async);
    return alive;
}

bool event_loop::on_loop_thread() const {
    return g_on_loop_thread;
}

bool event_loop::stop() {
    m_stopped.store(true, std::memory_order_release);
    if (m_loop == nullptr || on_loop_thread()) {
        return false;
    }
    if (m_thread != nullptr) {
        lock();
        m_thread_stop = true;
        // Wakes a loop thread waiting on `m_cond`; `lock` already made a running `uv_run` return.
        unlock();
        m_thread->join();
        delete m_thread;
        m_thread = nullptr;
    }
    return true;
}

void event_loop::restart() {
    if (exiting()) {
        return;
    }
    m_stopped.store(false, std::memory_order_release);
    if (m_thread == nullptr && m_loop != nullptr) {
        m_thread_stop = false;
        m_thread = new lthread([this]() { run(); });
    }
}

void event_loop::flush(uint64_t timeout_ms, bool (*pending)()) {
    // The loop thread still runs when the stop happened on it.
    if (exiting() || m_loop == nullptr || m_thread != nullptr) {
        return;
    }

    // Callbacks that check for the loop thread, such as a finalizer run by a continuation, must take
    // this thread for it.
    bool was_on_loop_thread = g_on_loop_thread;
    g_on_loop_thread = true;

    lock();
    // Inactive once it has fired.
    uv_timer_start(&m_flush_timer, [](uv_timer_t *) {}, timeout_ms, 0);
    unlock();

    // As in `run`: waiting threads take the lock between iterations, find the loop stopped, and fail
    // or clean up instead of waiting for the whole flush.
    while (true) {
        uv_mutex_lock(&m_mutex);
        while (m_waiters != 0) {
            uv_cond_wait(&m_cond, &m_mutex);
        }
        if (!uv_is_active((uv_handle_t*)&m_flush_timer) || !pending()) {
            uv_timer_stop(&m_flush_timer);
            uv_mutex_unlock(&m_mutex);
            break;
        }
        // The deadline timer bounds how long this blocks.
        uv_run(m_loop, UV_RUN_ONCE);
        uv_mutex_unlock(&m_mutex);
    }

    g_on_loop_thread = was_on_loop_thread;
}

void event_loop::stop_for_exit() {
    m_stopped.store(true, std::memory_order_release);
    // Recursive, so this also works on the loop thread. Taken before `exiting` is set: a finalizer that
    // then skips `uv_close` leaves `data` dangling, so no other thread may walk the handles or run the
    // loop by then.
    lock();
    m_exiting.store(true, std::memory_order_release);
}

// The loop thread's body.
void event_loop::run() {
    g_on_loop_thread = true;
    while (true) {
        uv_mutex_lock(&m_mutex);

        while (m_waiters != 0) {
            uv_cond_wait(&m_cond, &m_mutex);
        }

        // Checked with the lock held, since `alive` unreferences `m_async` under it.
        if (m_thread_stop || !uv_loop_alive(m_loop)) {
            uv_mutex_unlock(&m_mutex);
            break;
        }

        // `m_async` is always active, so the loop never runs out of things to wait on. A waiting thread
        // sends on it to make `uv_run` return, so that the mutex is released.
        uv_run(m_loop, UV_RUN_ONCE);

        uv_mutex_unlock(&m_mutex);
    }
}

/* Std.Internal.UV.Loop.configure (options : @& Loop.Options) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options) {
    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    int result = 0;

    {
        event_loop_guard guard;

        if (guard.stopped()) {
            result = UV_ECANCELED;
        } else if (accum) {
            result = uv_loop_configure(global_ev.m_loop, UV_METRICS_IDLE_TIME);
        }

        #if !defined(WIN32) && !defined(_WIN32)
        if (result == 0 && block) {
            result = uv_loop_configure(global_ev.m_loop, UV_LOOP_BLOCK_SIGNAL, SIGPROF);
        }
        #endif
    }

    if (result != 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.Loop.alive : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {
    event_loop_guard guard;
    return !guard.stopped() && global_ev.alive(guard);
}

#else

/* Std.Internal.UV.Loop.configure (options : @& Loop.Options) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options) {
    return io_result_mk_error("lean_uv_event_loop_configure is not supported");
}

/* Std.Internal.UV.Loop.alive : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {
    return 0;
}

#endif

}
