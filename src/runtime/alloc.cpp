/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lean/lean.h>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/alloc.h"

#ifdef _MSC_VER
extern "C" __declspec(thread) lean_runtime_tls lean_g_tls = {};
#else
extern "C" __thread lean_runtime_tls lean_g_tls = {};
#endif

namespace lean {

void initialize_alloc() {
}

void finalize_alloc() {
}

void set_heartbeats(uint64_t count) {
    lean_g_tls.heartbeat = count;
}

void add_heartbeats(uint64_t count) {
    lean_g_tls.heartbeat += count;
}

extern "C" LEAN_EXPORT void lean_inc_heartbeat() {
    add_heartbeats(1);
}

uint64_t get_num_heartbeats() {
    return lean_g_tls.heartbeat;
}

}
