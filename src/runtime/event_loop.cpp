/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/

#include "runtime/event_loop.h"

#ifndef LEAN_EMSCRIPTEN

using namespace std;

namespace lean {

// Utility function for error checking
static void check_uv(int result, const char *msg) {
    if (result != 0) {
        fprintf(stderr, "%s: %s\n", msg, uv_strerror(result));
        exit(EXIT_FAILURE);
    }
}

// The callback that stops the loop when it's called.
void async_callback(uv_async_t *handle) {
    uv_stop(handle->loop);
}

// Awakes the event loop and stops it so it can receive future requests.
void event_loop_wake(event_loop_t *event_loop) {
    int result = uv_async_send(&event_loop->async);
    (void)result;
    lean_assert(result == 0);
}

// Initializes the event loop
void event_loop_init(event_loop_t *event_loop) {
    event_loop->loop = uv_default_loop();
    check_uv(uv_mutex_init_recursive(&event_loop->mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&event_loop->cond_var), "Failed to initialize condition variable");
    check_uv(uv_async_init(event_loop->loop, &event_loop->async, NULL), "Failed to initialize async");
    event_loop->n_waiters = 0;
}

// Locks the event loop for the side of the requesters.
void event_loop_lock(event_loop_t *event_loop) {
    if (uv_mutex_trylock(&event_loop->mutex) != 0) {
        event_loop->n_waiters++;
        event_loop_wake(event_loop);
        uv_mutex_lock(&event_loop->mutex);
        event_loop->n_waiters--;
    }
}

// Unlock event loop
void event_loop_unlock(event_loop_t *event_loop) {
    uv_mutex_unlock(&event_loop->mutex);
    if (event_loop->n_waiters == 0) {
        uv_cond_signal(&event_loop->cond_var);
    }
}

// Runs the loop and stops when it needs to register new requests.
void event_loop_run_loop(event_loop_t *event_loop) {
    while (uv_loop_alive(event_loop->loop)) {
        uv_mutex_lock(&event_loop->mutex);

        if (event_loop->n_waiters != 0) {
            uv_cond_wait(&event_loop->cond_var, &event_loop->mutex);
        }

        if (event_loop->n_waiters == 0) {
            uv_run(event_loop->loop, UV_RUN_ONCE);
        }

        uv_mutex_unlock(&event_loop->mutex);
    }
}

}

#endif