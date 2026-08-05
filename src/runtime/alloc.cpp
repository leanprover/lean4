/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lean/lean.h>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/alloc.h"

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_NOINLINE __attribute__((noinline))
#else
#define LEAN_NOINLINE
#endif

namespace lean {

void initialize_alloc() {
#ifdef LEAN_MIMALLOC
    // MEASUREMENT PROBE, DO NOT MERGE: `0` disables transparent huge pages for Lean entirely, so a
    // benchmark run compares THP-off against the stock THP-on baseline. Locally that costs 2.7% of
    // cycles; no regression means the benchmark machine has no THP and this option is inert there.
    mi_option_set_default(mi_option_allow_thp, 0);
#endif
}

void finalize_alloc() {
}

LEAN_THREAD_VALUE(uint64_t, g_heartbeat, 0);

void set_heartbeats(uint64_t count) {
    g_heartbeat = count;
}

void add_heartbeats(uint64_t count) {
    g_heartbeat += count;
}

extern "C" LEAN_EXPORT void lean_inc_heartbeat() {
    add_heartbeats(1);
}

uint64_t get_num_heartbeats() {
    return g_heartbeat;
}

}
