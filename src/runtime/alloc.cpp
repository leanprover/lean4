/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <lean/lean.h>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/alloc.h"

#ifdef LEAN_RUNTIME_STATS
#define LEAN_RUNTIME_STAT_CODE(c) c
#else
#define LEAN_RUNTIME_STAT_CODE(c)
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_NOINLINE __attribute__((noinline))
#else
#define LEAN_NOINLINE
#endif

namespace lean {

void initialize_alloc() {
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


#ifdef LEAN_MIMALLOC
extern "C" mi_decl_restrict void* lean_alloc_small_mi_memory(mi_heap_t* heap, size_t size) mi_attr_noexcept {
    lean_inc_heartbeat();
    return mi_heap_malloc_small(heap, size);
}

#endif

uint64_t get_num_heartbeats() {
    return g_heartbeat;
}

}
