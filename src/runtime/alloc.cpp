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
    // Raise the minimal purge size to the platform's large page size: a `MADV_DONTNEED` over a
    // smaller range shatters a transparent-huge-page-backed region back into base pages, and Lean
    // frees far more than it returns to the OS. `set_default` keeps `MIMALLOC_ALLOW_THP` in the
    // environment authoritative.
    mi_option_set_default(mi_option_allow_thp, 2);
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
