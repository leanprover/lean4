/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues, Henrik Böving
*/
#include "runtime/uv/event_loop.h"
#include "runtime/thread.h"


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

// True on the thread currently running `finalize_libuv`. Used by `event_loop_wait_finalized` to
// recognise a re-entrant call from teardown itself.
static LEAN_THREAD_LOCAL bool g_in_teardown = false;

// Helpers

void lean_promise_resolve_with_code(int status, obj_arg promise) {
    obj_arg res = status == 0
        ? mk_except_ok(lean_box(0))
        : mk_except_err(lean_decode_uv_error(status, nullptr));

    lean_promise_resolve(res, promise);
}

void uv_deferred_teardown::run() {
    for (lean_object * promise : m_promises) {
        lean_promise_resolve_with_code(UV_ECANCELED, promise);
        lean_dec(promise);
    }

    m_promises.clear();

    for (lean_object * obj : m_releases) {
        lean_dec(obj);
    }

    m_releases.clear();
}

// Utility function for error checking. This function is only used inside the
// initializition of the event loop.
static void check_uv(int result, const char * msg) {
    if (result != 0) {
        std::string err_message = std::string(msg) + ": " + uv_strerror(result);
        lean_internal_panic(err_message.c_str());
    }
}

// Interrupts the event loop and stops it so it can receive future requests.
//
// The guard shares `interrupt_mutex` with the teardown store to `state`, which is what keeps a send
// away from an `async` handle being closed: the teardown walk closes it strictly after that store.
static void event_loop_interrupt(event_loop_t * event_loop) {
    uv_mutex_lock(&event_loop->interrupt_mutex);

    if (event_loop->state == EVENT_LOOP_RUNNING) {
        int result = uv_async_send(&event_loop->async);
        (void)result;
        lean_assert(result == 0);
    }

    uv_mutex_unlock(&event_loop->interrupt_mutex);
}

// Initializes the event loop
void event_loop_init(event_loop_t * event_loop) {
    event_loop->loop = uv_default_loop();
    check_uv(uv_mutex_init_recursive(&event_loop->mutex), "Failed to initialize mutex");
    check_uv(uv_mutex_init(&event_loop->interrupt_mutex), "Failed to initialize interrupt mutex");
    check_uv(uv_mutex_init(&event_loop->finalize_mutex), "Failed to initialize finalize mutex");
    check_uv(uv_cond_init(&event_loop->cond_var), "Failed to initialize condition variable");
    check_uv(uv_cond_init(&event_loop->finalize_cond), "Failed to initialize finalize condition variable");
    check_uv(uv_async_init(event_loop->loop, &event_loop->async, NULL), "Failed to initialize async");
    event_loop->n_waiters = 0;
    event_loop->state = EVENT_LOOP_RUNNING;
    event_loop->requests = nullptr;
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

// Locks the event loop for the side of the requesters, failing once teardown has begun.
//
// The leading read is unsynchronized and only skips work: `state` only ever changes while the
// mutex is held, so a requester that still sees `RUNNING` after teardown stored `STOPPING` goes on
// to take the mutex and the recheck below turns it away. Its interrupt is harmless for the same
// reason `event_loop_interrupt` is safe.
bool event_loop_lock(event_loop_t * event_loop) {
    if (event_loop->state != EVENT_LOOP_RUNNING) {
        return false;
    }

    event_loop_lock_internal(event_loop);

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

// Closes the loop to new requesters and wakes the loop thread so it can observe that.
void event_loop_request_stop(event_loop_t * event_loop) {
    uv_mutex_lock(&event_loop->interrupt_mutex);
    event_loop->state = EVENT_LOOP_STOPPING;
    uv_mutex_unlock(&event_loop->interrupt_mutex);

    // Sent directly rather than through `event_loop_interrupt`, which now declines: the teardown
    // walk that closes `async` has not run yet, so the handle is still live.
    int result = uv_async_send(&event_loop->async);
    (void)result;
    lean_assert(result == 0);

    uv_cond_signal(&event_loop->cond_var);
}

// Marks the calling thread as the one running `finalize_libuv`.
void event_loop_begin_teardown() {
    g_in_teardown = true;
}

void event_loop_mark_finalized(event_loop_t * event_loop) {
    uv_mutex_lock(&event_loop->finalize_mutex);
    event_loop->state = EVENT_LOOP_FINALIZED;
    uv_cond_broadcast(&event_loop->finalize_cond);
    uv_mutex_unlock(&event_loop->finalize_mutex);
}

// Blocks until `finalize_libuv` has marked the loop finalized. Handle finalizers use this when they
// find the loop gone: by the time the loop is finalized the teardown walk has already detached
// (nulled) and closed their `uv_handle_t`, so they can free the wrapping struct without racing the
// walk.
//
// This waits on `finalize_mutex` rather than `mutex`: a finalizer can be reached from a thread that
// already holds `mutex`, and `uv_cond_wait` on a recursive mutex held more than once is undefined.
void event_loop_wait_finalized(event_loop_t * event_loop) {
    if (g_in_teardown) {
        return;
    }

    uv_mutex_lock(&event_loop->finalize_mutex);
    while (event_loop->state != EVENT_LOOP_FINALIZED) {
        uv_cond_wait(&event_loop->finalize_cond, &event_loop->finalize_mutex);
    }
    uv_mutex_unlock(&event_loop->finalize_mutex);
}

void event_loop_register_request(event_loop_t * event_loop, uv_pending_req * pending, uv_req_t * req, lean_object * promise, lean_object * owned) {
    pending->req = req;
    pending->promise = promise;
    pending->owned = owned;
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
// threadpool; those complete promptly with `UV_ECANCELED` through their normal callback.
void event_loop_cancel_requests(event_loop_t * event_loop) {
    for (uv_pending_req * pending = event_loop->requests; pending != nullptr; pending = pending->next) {
        uv_cancel(pending->req);
    }
}

// Abandons the requests that outlived the teardown drain, returning whether there were any.
//
// Their `uv_req_t`s stay registered and allocated: a threadpool worker still owns the memory and
// will write to it, so the loop is deliberately left unclosed rather than freed underneath it.
//
// `owned` is released here rather than leaked with the request, which is why a registered request
// may never hand a worker memory that `owned` keeps alive; `lean_uv_random` allocates its scratch
// buffer inside the request for exactly this reason.
//
// Settling the promises runs Lean code, so it is deferred alongside the walk's rather than done
// under the loop lock.
bool event_loop_abandon_requests(event_loop_t * event_loop, uv_deferred_teardown & deferred) {
    bool abandoned = false;

    for (uv_pending_req * pending = event_loop->requests; pending != nullptr; pending = pending->next) {
        if (pending->promise != nullptr) {
            deferred.cancel_promise(pending->promise);
            pending->promise = nullptr;
        }

        if (pending->owned != nullptr) {
            deferred.release(pending->owned);
            pending->owned = nullptr;
        }

        abandoned = true;
    }

    return abandoned;
}

lean_obj_res lean_uv_loop_unavailable_error() {
    // The message is the error's `details`; `lean_decode_uv_error` would take it as a file name,
    // which `UV_ECANCELED` does not accept.
    lean_object * details = lean_mk_string("libuv event loop is not available");
    return lean_io_result_mk_error(lean_mk_io_error_other_error(-UV_ECANCELED, details));
}

// Runs the loop and stops when it needs to register new requests.
void event_loop_run_loop(event_loop_t * event_loop) {
    while (true) {
        uv_mutex_lock(&event_loop->mutex);

        while (event_loop->n_waiters != 0 && event_loop->state == EVENT_LOOP_RUNNING) {
            uv_cond_wait(&event_loop->cond_var, &event_loop->mutex);
        }

        if (event_loop->state != EVENT_LOOP_RUNNING) {
            uv_mutex_unlock(&event_loop->mutex);
            break;
        }

        // `UV_RUN_ONCE` returns after servicing one round of events. `async` is always active, so
        // the loop never runs out of things to wait on; a requester wakes it with `uv_async_send`
        // and this unlock is what lets that requester in.
        uv_run(event_loop->loop, UV_RUN_ONCE);

        uv_mutex_unlock(&event_loop->mutex);
    }
}

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : IO Unit */
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

    return lean_io_result_mk_ok(lean_box(0));
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

/* Std.Internal.UV.Loop.configure (options : Loop.Options) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_configure(b_obj_arg options) {
    return io_result_mk_error("lean_uv_event_loop_configure is not supported");
}

/* Std.Internal.UV.Loop.alive : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {
    return 0;
}

#endif

}
