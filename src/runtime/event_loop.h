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

typedef struct {
    uv_loop_t *loop;
    uv_mutex_t mutex;
    uv_cond_t cond_var;
    uv_async_t async;
    _Atomic(int) n_waiters;
} event_loop_t;

void event_loop_init(event_loop_t *event_loop);
void event_loop_cleanup(event_loop_t *event_loop);
void event_loop_lock(event_loop_t *event_loop);
void event_loop_unlock(event_loop_t *event_loop);
void event_loop_wake(event_loop_t *event_loop);
void event_loop_run_loop(event_loop_t *event_loop);

}

#endif