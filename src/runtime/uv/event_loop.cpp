/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/event_loop.h"


/*
This file builds a thread safe event loop on top of the thread unsafe libuv event loop.
We achieve this by always having a `uv_async_t` associated with the libuv event loop.
As `uv_async_t` are a thread safe primitive it is safe to send a notification to it from another
thread. Once this notification arrives the event loop suspends its own execution and unlocks a mutex
that protects it. This mutex can then be taken by another thread that wants to work with the event
loop. After that work is done it signals a condition variable that the event loop is waiting on
to continue its execution.
*/

namespace lean {
#ifndef LEAN_EMSCRIPTEN
using namespace std;

event_loop_t global_ev;

// Helpers

void lean_promise_resolve_with_code(int status, obj_arg promise) {
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

// The callback that stops the loop when it's called.
void async_callback(uv_async_t * handle) {
    uv_stop(handle->loop);
}

// Interrupts the event loop and stops it so it can receive future requests.
void event_loop_interrupt(event_loop_t * event_loop) {
    int result = uv_async_send(&event_loop->async);
    (void)result;
    lean_assert(result == 0);
}

// Initializes the event loop
void event_loop_init(event_loop_t * event_loop) {
    event_loop->loop = uv_default_loop();
    check_uv(uv_mutex_init_recursive(&event_loop->mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&event_loop->cond_var), "Failed to initialize condition variable");
    check_uv(uv_cond_init(&event_loop->finalize_cond), "Failed to initialize finalize condition variable");
    check_uv(uv_async_init(event_loop->loop, &event_loop->async, NULL), "Failed to initialize async");
    event_loop->n_waiters = 0;
    event_loop->n_active = 0;
    event_loop->state = EVENT_LOOP_RUNNING;
    event_loop->requests = nullptr;
}

// Leaves the drain region entered in `event_loop_lock`. While finalizing, the last requester to
// leave wakes `event_loop_drain_active`; during normal operation this is just an atomic decrement.
static void event_loop_active_release(event_loop_t * event_loop) {
    if (--event_loop->n_active == 0 && event_loop->state != EVENT_LOOP_RUNNING) {
        uv_mutex_lock(&event_loop->mutex);
        uv_cond_signal(&event_loop->cond_var);
        uv_mutex_unlock(&event_loop->mutex);
    }
}

// Acquires the loop mutex, interrupting the loop if another thread is running it. Unlike
// `event_loop_lock`, does not consult `state`, so it locks even while finalizing; used by
// `finalize_libuv` itself.
void event_loop_lock_internal(event_loop_t * event_loop) {
    lean_assert(event_loop->state != EVENT_LOOP_UNINITIALIZED);
    if (uv_mutex_trylock(&event_loop->mutex) != 0) {
        event_loop->n_waiters++;
        event_loop_interrupt(event_loop);
        uv_mutex_lock(&event_loop->mutex);
        event_loop->n_waiters--;
    }
}

// Locks the event loop for the side of the requesters.
//
// Registers in `n_active` before reading `state` so that a concurrent `finalize_libuv` cannot close
// the interrupt `async` (in `event_loop_drain_active`) between our `state` check and the
// `uv_async_send` inside `event_loop_lock_internal`: it waits for `n_active` to drain first.
// Requesters arriving after the loop has left `RUNNING` bail out before they would ever interrupt.
bool event_loop_lock(event_loop_t * event_loop) {
    event_loop->n_active++;

    if (event_loop->state != EVENT_LOOP_RUNNING) {
        event_loop_active_release(event_loop);
        return false;
    }

    event_loop_lock_internal(event_loop);
    event_loop_active_release(event_loop);

    if (event_loop->state != EVENT_LOOP_RUNNING) {
        event_loop_unlock(event_loop);
        return false;
    }

    return true;
}

// Unlock event loop
void event_loop_unlock(event_loop_t * event_loop) {
    if (event_loop->n_waiters == 0) {
        uv_cond_signal(&event_loop->cond_var);
    }
    uv_mutex_unlock(&event_loop->mutex);
}

void event_loop_request_stop(event_loop_t * event_loop) {
    event_loop->state = EVENT_LOOP_STOPPING;
    event_loop_interrupt(event_loop);
    uv_cond_signal(&event_loop->cond_var);
}

void event_loop_drain_active(event_loop_t * event_loop) {
    uv_mutex_lock(&event_loop->mutex);

    while (event_loop->n_active != 0) {
        uv_cond_wait(&event_loop->cond_var, &event_loop->mutex);
    }

    uv_mutex_unlock(&event_loop->mutex);
}

void event_loop_mark_finalized(event_loop_t * event_loop) {
    event_loop->state = EVENT_LOOP_FINALIZED;
    uv_cond_broadcast(&event_loop->finalize_cond);
}

// Blocks until `finalize_libuv` has marked the loop finalized. Handle finalizers use this when they
// find the loop gone: by the time the loop is finalized the teardown walk has already detached
// (nulled) and closed their `uv_handle_t`, so they can free the wrapping struct without racing the
// walk. Re-entrant calls from the teardown thread itself return immediately (the mutex is recursive
// and the state is already finalized).
void event_loop_wait_finalized(event_loop_t * event_loop) {
    uv_mutex_lock(&event_loop->mutex);
    while (event_loop->state != EVENT_LOOP_FINALIZED) {
        uv_cond_wait(&event_loop->finalize_cond, &event_loop->mutex);
    }
    uv_mutex_unlock(&event_loop->mutex);
}

void event_loop_register_request(event_loop_t * event_loop, uv_pending_req * pending, uv_req_t * req,
                                 lean_object * promise) {
    pending->req = req;
    pending->promise = promise;
    pending->prev = nullptr;
    pending->next = event_loop->requests;

    if (event_loop->requests != nullptr) {
        event_loop->requests->prev = pending;
    }

    event_loop->requests = pending;
}

void event_loop_unregister_request(event_loop_t * event_loop, uv_pending_req * pending) {
    if (pending->prev != nullptr) {
        pending->prev->next = pending->next;
    } else {
        event_loop->requests = pending->next;
    }

    if (pending->next != nullptr) {
        pending->next->prev = pending->prev;
    }

    pending->prev = nullptr;
    pending->next = nullptr;
}

// Asks libuv to cancel every tracked request. This only succeeds for requests still queued in the
// threadpool; those complete promptly with `UV_ECANCELED` through their normal callback. Requests
// already executing in a worker (a `getaddrinfo` inside the OS resolver) cannot be interrupted and
// are left for `event_loop_detach_requests`.
void event_loop_cancel_requests(event_loop_t * event_loop) {
    for (uv_pending_req * pending = event_loop->requests; pending != nullptr; pending = pending->next) {
        uv_cancel(pending->req);
    }
}

bool event_loop_has_requests(event_loop_t * event_loop) {
    return event_loop->requests != nullptr;
}

// Abandons the requests that outlived the teardown drain, returning how many there were.
//
// Their promises are resolved with `UV_ECANCELED` so nothing waits on them forever, but neither the
// request nor its buffers are freed: a threadpool worker may still be writing into them (`uv_random`
// fills a `ByteArray` in place), and there is no way to wait for it. Leaking a bounded number of
// requests at process exit is the price of not blocking on an uninterruptible syscall. This is safe
// only because the loop is never run again after `finalize_libuv`, so the completion callbacks
// cannot fire and double-release the promise.
size_t event_loop_detach_requests(event_loop_t * event_loop) {
    size_t abandoned = 0;

    for (uv_pending_req * pending = event_loop->requests; pending != nullptr; pending = pending->next) {
        if (pending->promise != nullptr) {
            lean_promise_resolve_with_code(UV_ECANCELED, pending->promise);
            lean_dec(pending->promise);
            pending->promise = nullptr;
        }

        abandoned++;
    }

    return abandoned;
}

lean_obj_res lean_uv_loop_unavailable_error() {
    // `lean_decode_uv_error` borrows the message.
    lean_object * msg = lean_mk_string("libuv event loop is not available");
    lean_obj_res res = lean_io_result_mk_error(lean_decode_uv_error(UV_ECANCELED, msg));
    lean_dec_ref(msg);
    return res;
}

// Runs the loop and stops when it needs to register new requests.
void event_loop_run_loop(event_loop_t * event_loop) {
    while (true) {
        uv_mutex_lock(&event_loop->mutex);

        while (event_loop->n_waiters != 0 && event_loop->state == EVENT_LOOP_RUNNING) {
            uv_cond_wait(&event_loop->cond_var, &event_loop->mutex);
        }

        // The interrupt async is always active, so `uv_loop_alive` never becomes false; the loop only
        // exits once finalization moves it out of the RUNNING state.
        if (event_loop->state != EVENT_LOOP_RUNNING) {
            uv_mutex_unlock(&event_loop->mutex);
            break;
        }

        uv_run(event_loop->loop, UV_RUN_ONCE);
        /*
         * We leave `uv_run` only when `uv_stop` is called as there is always the `uv_async_t` so
         * we can never run out of things to wait on. `uv_stop` is only called from `async_callback`
         * when another thread wants to work with the event loop so we need to give up the mutex.
         */

        uv_mutex_unlock(&event_loop->mutex);
    }
}

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options) {
    bool accum = lean_ctor_get_uint8(options, 0);
    bool block = lean_ctor_get_uint8(options, 1);

    if (!event_loop_lock(&global_ev)) {
        return lean_uv_loop_unavailable_error();
    }

    if (accum) {
        int result = uv_loop_configure(global_ev.loop, UV_METRICS_IDLE_TIME);
        if (result != 0) {
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        }
    }

    #if!defined(WIN32) && !defined(_WIN32)
    if (block) {
        int result = uv_loop_configure(global_ev.loop, UV_LOOP_BLOCK_SIGNAL, SIGPROF);
        if (result != 0) {
            event_loop_unlock(&global_ev);
            return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
        }
    }
    #endif

    event_loop_unlock(&global_ev);

    return lean_box(0);
}

/* Std.Internal.UV.Loop.alive : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {
    if (!event_loop_lock(&global_ev)) {
        return 0;
    }
    int is_alive = uv_loop_alive(global_ev.loop);
    event_loop_unlock(&global_ev);

    return is_alive;
}

void initialize_libuv_loop() {
    event_loop_init(&global_ev);
}

#else

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options) {
    return io_result_mk_error("lean_uv_event_loop_configure is not supported");
}

/* Std.Internal.UV.Loop.alive : BaseIO UInt64 */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive() {
    return io_result_mk_error("lean_uv_event_loop_alive is not supported");
}

#endif

}
