/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/
/*
Compiles all of mimalloc (`static.c`) together with the runtime's small-object allocation entry
point in a single translation unit so that mimalloc's allocation fast path inlines into it:
compiled Lean code reaches the allocator, including the heartbeat update, with a single call.
`static.c` must come before any Lean header so that mimalloc's headers configure themselves from
this variant's `MI_*` flags (see `add_mimalloc_variant` in `CMakeLists.txt`) before
`lean/mimalloc.h` is seen.
*/
#include "runtime/alloc_tls.h"
/* Host mimalloc's default-theap storage in `lean_g_tls` (see `script/mimalloc-lean.patch`), so
   that the entry point below updates the heartbeat and reads the theap with a single TLS address
   computation. Only effective under `MI_TLS_MODEL_LOCAL` (e.g. Linux); the other TLS models keep
   the theap in OS-managed slots and `lean_g_tls.mi_theap_default` stays unused. */
#define MI_THEAP_DEFAULT_TLS_FIELD (lean_g_tls.mi_theap_default)
#include <static.c>
// mimalloc's `atomic.h` already defined `_Atomic` for C++; `lean.h` redefines it identically
#undef _Atomic
#include <lean/lean.h>
#include "runtime/alloc.h"

/* Same initial value as mimalloc's own default-theap thread-local: the empty theap routes the
   first allocation of a thread into the generic path, which creates the real theap and stores it
   back through `_mi_theap_default_set`. */
#ifdef _MSC_VER
extern "C" __declspec(thread) lean_runtime_tls lean_g_tls = { 0, (mi_theap_t*)&_mi_theap_empty };
#else
extern "C" __thread lean_runtime_tls lean_g_tls = { 0, (mi_theap_t*)&_mi_theap_empty };
#endif

extern "C" LEAN_EXPORT LEAN_ATTR_MALLOC lean_object * lean_alloc_small_object_core(unsigned sz) {
    lean_runtime_tls * tls = &lean_g_tls;
    tls->heartbeat++;
    // the callers guarantee `sz > 0 && sz % LEAN_OBJECT_SIZE_DELTA == 0 && sz <= MI_SMALL_SIZE_MAX`
#if MI_TLS_MODEL_LOCAL
    void * mem = mi_theap_malloc_small(tls->mi_theap_default, sz);
#else
    void * mem = mi_malloc_small(sz);
#endif
    if (LEAN_UNLIKELY(mem == NULL)) lean_internal_panic_out_of_memory();
    lean_object * o = (lean_object *)mem;
    /* `m_cs_sz` must be the exact (aligned) requested size, not mimalloc's potentially larger
       block size: `lean_small_object_size` and `leangz` rely on it. */
    o->m_cs_sz = sz;
    return o;
}
