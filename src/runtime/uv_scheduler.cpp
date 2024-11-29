/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/

#include "runtime/uv_scheduler.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <uv.h>

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

void scheduler_wake(scheduler_t *scheduler) {
    uv_async_send(&scheduler->async);
}

// Initialize scheduler
void scheduler_init(scheduler_t *scheduler) {
    scheduler->loop = uv_default_loop();
    check_uv(uv_mutex_init_recursive(&scheduler->mutex), "Failed to initialize mutex");
    check_uv(uv_cond_init(&scheduler->cond_var), "Failed to initialize condition variable");
    check_uv(uv_async_init(scheduler->loop, &scheduler->async, NULL), "Failed to initialize async");
    scheduler->n_waiters = 0;
}

// Locks the scheduler for the side of the requesters.
void scheduler_lock(scheduler_t *scheduler) {
    if (uv_mutex_trylock(&scheduler->mutex) != 0) {
        scheduler->n_waiters++;
        scheduler_wake(scheduler);
        uv_mutex_lock(&scheduler->mutex);
        scheduler->n_waiters--;
    }
}

// Unlock scheduler
void scheduler_unlock(scheduler_t *scheduler) {
    uv_mutex_unlock(&scheduler->mutex);
    if (scheduler->n_waiters == 0) {
        uv_cond_signal(&scheduler->cond_var);
    }
}

// Scheduler run loop
void scheduler_run_loop(scheduler_t *scheduler) {
    while (uv_loop_alive(scheduler->loop)) {
        uv_mutex_lock(&scheduler->mutex);

        if (scheduler->n_waiters != 0) {
            uv_cond_wait(&scheduler->cond_var, &scheduler->mutex);
        }

        if (scheduler->n_waiters == 0) {
            uv_run(scheduler->loop, UV_RUN_ONCE);
        }

        uv_mutex_unlock(&scheduler->mutex);
    }
}

}