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
extern "C" __declspec(thread) uint64_t lean_g_heartbeat = 0;
#else
extern "C" __thread uint64_t lean_g_heartbeat = 0;
#endif

namespace lean {

void initialize_alloc() {
}

void finalize_alloc() {
}

void set_heartbeats(uint64_t count) {
    lean_g_heartbeat = count;
}

void add_heartbeats(uint64_t count) {
    lean_g_heartbeat += count;
}

extern "C" LEAN_EXPORT void lean_inc_heartbeat() {
    add_heartbeats(1);
}

uint64_t get_num_heartbeats() {
    return lean_g_heartbeat;
}

#ifdef LEAN_MIMALLOC
extern "C" LEAN_EXPORT LEAN_ATTR_MALLOC lean_object * lean_alloc_small_object_core(unsigned sz) {
    lean_g_heartbeat++;
    // the callers guarantee `sz > 0 && sz % LEAN_OBJECT_SIZE_DELTA == 0 && sz <= MI_SMALL_SIZE_MAX`
    void * mem = mi_malloc_small(sz);
    if (LEAN_UNLIKELY(mem == NULL)) lean_internal_panic_out_of_memory();
    lean_object * o = (lean_object *)mem;
    /* `m_cs_sz` must be the exact (aligned) requested size, not mimalloc's potentially larger
       block size: `lean_small_object_size` and `leangz` rely on it. */
    o->m_cs_sz = sz;
    return o;
}
#endif

}
