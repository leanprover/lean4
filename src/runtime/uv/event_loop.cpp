/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/event_loop.h"
#include "runtime/thread.h"
#include <cstring>

namespace lean {
#ifndef LEAN_EMSCRIPTEN
using namespace std;

event_loop global_ev;

// Helpers

void lean_promise_resolve_with_code(int status, b_obj_arg promise) {
    obj_arg res = status == 0
        ? mk_except_ok(lean_box(0))
        : mk_except_err(lean_decode_uv_error(status, nullptr));

    lean_promise_resolve(res, promise);
}

// Utility function for error checking. This function is only used inside the
// initializition of the event loop.
static void check_uv(int result, const char * msg) {
    if (result != 0) {
        std::string err_message = std::string(msg) + ": " + uv_strerror(result);
        lean_internal_panic(err_message.c_str());
    }
}

void event_loop::start() {
    m_loop = uv_default_loop();
    check_uv(uv_mutex_init_recursive(&m_mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&m_cond), "Failed to initialize condition variable");
    check_uv(uv_async_init(m_loop, &m_async, nullptr), "Failed to initialize async");
    m_waiters = 0;

    lthread([this]() { run(); });
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

// `nullptr` if `size` is a valid receive buffer size. libuv reports an empty buffer as `UV_ENOBUFS`,
// which would read as a resource shortage.
lean_obj_res lean_uv_recv_size_error(uint64_t size) {
    if (size != 0) {
        return nullptr;
    }
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, lean_mk_string("receive buffer size must be positive")));
}

// Sets the size of a receive buffer to the `nread` bytes it received. A read that fills less than half
// of it is moved to a buffer of its own size instead, so that many small reads do not each keep a
// full-sized buffer alive.
lean_object * lean_uv_fit_read_buffer(lean_object * byte_array, size_t nread) {
    if (nread * 2 >= lean_sarray_capacity(byte_array)) {
        lean_sarray_set_size(byte_array, nread);
        return byte_array;
    }
    lean_object * fitted = lean_alloc_sarray(1, nread, nread);
    memcpy(lean_sarray_cptr(fitted), lean_sarray_cptr(byte_array), nread);
    lean_dec(byte_array);
    return fitted;
}

// The loop thread's body.
void event_loop::run() {
    while (true) {
        uv_mutex_lock(&m_mutex);

        while (m_waiters != 0) {
            uv_cond_wait(&m_cond, &m_mutex);
        }

        // Checked with the lock held, since `alive` unreferences `m_async` under it.
        if (!uv_loop_alive(m_loop)) {
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
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
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
