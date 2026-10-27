/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/event_loop.h"
#include "runtime/uv/signal.h"
#include "runtime/uv/tcp.h"
#include "runtime/uv/timer.h"
#include "runtime/uv/udp.h"
#include "runtime/thread.h"
#include <cstdio>
#include <type_traits>

namespace lean {
#ifndef LEAN_EMSCRIPTEN
event_loop global_ev;

// Utility function for error checking. This function is only used inside the
// initializition of the event loop.
static void check_uv(int result, const char * msg) {
    if (result != 0) {
        std::string err_message = std::string(msg) + ": " + uv_strerror(result);
        lean_internal_panic(err_message.c_str());
    }
}

void event_loop::start() {
    // A loop of our own: the teardown treats every handle on it as one of ours.
    m_loop = &m_loop_storage;
    check_uv(uv_loop_init(m_loop), "Failed to initialize loop");
    check_uv(uv_mutex_init_recursive(&m_mutex), "Failed to initialize mutex");
    check_uv(uv_mutex_init(&m_async_mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&m_cond), "Failed to initialize condition variable");
    check_uv(uv_async_init(m_loop, &m_async, nullptr), "Failed to initialize async");
    m_waiters = 0;
    m_running = true;

    m_thread = new lthread([this]() { run(); });
}

void event_loop::lock() {
    if (uv_mutex_trylock(&m_mutex) != 0) {
        m_waiters++;
        // `stop` closes `m_async` once it is no longer running.
        uv_mutex_lock(&m_async_mutex);
        if (m_running) {
            int result = uv_async_send(&m_async);
            (void)result;
            lean_assert(result == 0);
        }
        uv_mutex_unlock(&m_async_mutex);
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

// The loop thread's body.
void event_loop::run() {
    while (true) {
        uv_mutex_lock(&m_mutex);

        while (m_waiters != 0) {
            uv_cond_wait(&m_cond, &m_mutex);
        }

        // Checked with the lock held, since `alive` unreferences `m_async` under it.
        if (!m_running || !uv_loop_alive(m_loop)) {
            uv_mutex_unlock(&m_mutex);
            break;
        }

        // `m_async` is always active, so the loop never runs out of things to wait on. A waiting thread
        // sends on it to make `uv_run` return, so that the mutex is released.
        uv_run(m_loop, UV_RUN_ONCE);

        uv_mutex_unlock(&m_mutex);
    }
}

void event_loop::exit_drop(owned_ref ref) {
    m_released.push_back(std::move(ref));
}

// Hands the Lean references of a handle's object to the loop: the loop's own references to the object,
// then the ones the object holds. The handle is the object's first member.
template<class T>
static void drop_handle_refs(uv_handle_t * handle) {
    static_assert(std::is_standard_layout_v<T>);
    T * object = reinterpret_cast<T *>(handle);
    for (unsigned n = object->loop_refs(); n > 0; n--) {
        global_ev.exit_drop(owned_ref((lean_object *)handle->data));
    }
    for (owned_ref * ref : object->lean_refs()) {
        global_ev.exit_drop(std::move(*ref));
    }
}

static void close_for_exit(uv_handle_t * handle, void *) {
    // A finalizer closes its handle itself, and the close callback frees the object.
    if (uv_is_closing(handle)) {
        return;
    }

    switch (handle->type) {
        case UV_TIMER:
            drop_handle_refs<lean_uv_timer_object>(handle);
            break;
        case UV_SIGNAL:
            drop_handle_refs<lean_uv_signal_object>(handle);
            break;
        case UV_TCP:
            drop_handle_refs<lean_uv_tcp_socket_object>(handle);
            break;
        case UV_UDP:
            drop_handle_refs<lean_uv_udp_socket_object>(handle);
            break;
        case UV_ASYNC:
            break;
        default:
            lean_internal_panic("unexpected libuv handle at exit");
    }

    // The object is freed by its finalizer, which finds the handle closed.
    uv_close(handle, nullptr);
}

void event_loop::stop() {
    if (m_thread == nullptr) {
        return;
    }

    lock();
    uv_mutex_lock(&m_async_mutex);
    m_running = false;
    uv_mutex_unlock(&m_async_mutex);
    unlock();

    // Waits for a callback the loop thread is running, including a `(sync := true)` continuation, so one
    // that blocks delays the exit for as long as it blocks.
    m_thread->join();
    delete m_thread;
    m_thread = nullptr;

    std::vector<owned_ref> released;
    {
        event_loop_guard guard;

        uv_walk(m_loop, close_for_exit, nullptr);

        // Closing a handle cancels its requests, and threadpool requests run to completion. Their callbacks
        // hand their references to `exit_drop`.
        uv_run(m_loop, UV_RUN_DEFAULT);

        int result = uv_loop_close(m_loop);
        if (result != 0) {
            fprintf(stderr, "warning: libuv event loop did not close at exit: %s\n", uv_strerror(result));
        }

        released = std::move(m_released);
    }
    // Released after the unlock: the finalizers this runs take the lock themselves.
}

/* Std.Internal.UV.Loop.configure (options : @& Loop.Options) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options) {
    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    int result = 0;

    {
        event_loop_guard guard;

        if (accum) {
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
    return global_ev.alive(guard);
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
