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
}

void finalize_alloc() {
}

extern "C" {
#ifdef LEAN_HEARTBEAT_TLS
LEAN_EXPORT __thread uint64_t lean_heartbeat LEAN_HEARTBEAT_TLS = 0;
#else
LEAN_THREAD_VALUE(uint64_t, lean_heartbeat, 0);
#endif
}

void set_heartbeats(uint64_t count) {
    lean_heartbeat = count;
}

void add_heartbeats(uint64_t count) {
    lean_heartbeat += count;
}

extern "C" LEAN_EXPORT void lean_inc_heartbeat() {
    add_heartbeats(1);
}

#if defined(LEAN_MIMALLOC) && defined(LEAN_HEARTBEAT_TLS)
/* Stand-in for a real theap, used as the initial value of the per-thread cache below so that the
   inline fast path in `lean.h` never has to test for a null cache. Every size class resolves to a
   page whose free list is empty, which sends the caller down the slow path, and that installs the
   real theap. Only the two fields the fast path reads are modelled, and neither is ever written,
   since the write only happens once a block has been popped. Being a constant initialiser this
   covers every thread, including ones that never run any Lean initialisation. */
static void * g_mi_empty_page[4] = { 0, 0, 0, 0 };   /* the `free` field, at offset 8, is null */

#define LEAN_MI_P1  ((void *)g_mi_empty_page)
#define LEAN_MI_P8  LEAN_MI_P1, LEAN_MI_P1, LEAN_MI_P1, LEAN_MI_P1, LEAN_MI_P1, LEAN_MI_P1, LEAN_MI_P1, LEAN_MI_P1
#define LEAN_MI_P64 LEAN_MI_P8, LEAN_MI_P8, LEAN_MI_P8, LEAN_MI_P8, LEAN_MI_P8, LEAN_MI_P8, LEAN_MI_P8, LEAN_MI_P8

static struct {
    char   m_prefix[0x118];
    void * m_pages_free_direct[MI_SMALL_SIZE_MAX / sizeof(void *) + 1];
} g_mi_empty_theap = { { 0 }, { LEAN_MI_P64, LEAN_MI_P64, LEAN_MI_P1 } };

static_assert(MI_SMALL_SIZE_MAX / sizeof(void *) + 1 == 129,
              "size-class table shape changed; the empty-theap stand-in must be resized");

extern "C" {
LEAN_EXPORT __thread void * lean_mi_theap LEAN_HEARTBEAT_TLS = &g_mi_empty_theap;

/* Kept out of line so the inline fast path never writes to `lean_mi_theap`: a write would keep the
   thread-pointer address live across the call and cost the caller two extra callee-saved spills. */
LEAN_EXPORT void * lean_mi_malloc_small_slow(size_t sz) {
    void * p = mi_malloc_small(sz);
    lean_mi_theap = mi_theap_get_default();
    return p;
}
}
#endif

uint64_t get_num_heartbeats() {
    return lean_heartbeat;
}

}
