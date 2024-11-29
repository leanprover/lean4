/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/debug.h"

#ifndef LEAN_EMSCRIPTEN

using namespace std;
#include <uv.h>

namespace lean {

// Scheduler structure
typedef struct {
    uv_loop_t *loop;
    pthread_mutex_t mutex;
    uv_cond_t cond_var;
    uv_async_t async;
    _Atomic(int) n_waiters;
} scheduler_t;

// Scheduler API
void scheduler_init(scheduler_t *scheduler);
void scheduler_cleanup(scheduler_t *scheduler);
void scheduler_lock(scheduler_t *scheduler);
void scheduler_unlock(scheduler_t *scheduler);
void scheduler_wake(scheduler_t *scheduler);
void scheduler_run_loop(scheduler_t *scheduler);

}

#endif