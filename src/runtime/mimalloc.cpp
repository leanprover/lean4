/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/

/*
Compiles all of mimalloc (`static.c`) together with the runtime's small-object allocation entry
point in a single translation unit so that mimalloc's allocation fast path inlines into it:
compiled Lean code reaches the allocator, including the heartbeat update, with a single call.
`static.c` must come first so that mimalloc's headers configure themselves from this variant's
`MI_*` flags (see `add_mimalloc_variant` in `CMakeLists.txt`) before `lean/mimalloc.h` is seen.
*/
#include <static.c>

// mimalloc's `atomic.h` already defined `_Atomic` for C++; `lean.h` redefines it identically
#undef _Atomic

#include <lean/lean.h>
#include "runtime/alloc.h"
#include "runtime/debug.h"

/* The initial cache value is mimalloc's read-only empty theap — the same sentinel mimalloc uses
   for its own default-theap thread-local: its free-page lookup always misses, routing allocations
   into the generic path, which handles an uninitialized theap. This keeps the fast path free of
   an initialization check while threads that skip `lean_mi_theap_cache_init` stay correct. The
   sentinel is internal to mimalloc but part of this translation unit. */
#ifdef _MSC_VER
extern "C" __declspec(thread) lean_runtime_tls lean_g_tls = { 0, (mi_theap_t*)&_mi_theap_empty };
#else
extern "C" __thread lean_runtime_tls lean_g_tls = { 0, (mi_theap_t*)&_mi_theap_empty };
#endif

extern "C" void lean_mi_theap_cache_init(void) {
    lean_g_tls.mi_theap_default = mi_theap_get_default();
}

/* The callers guarantee `sz > 0 && sz % LEAN_OBJECT_SIZE_DELTA == 0 && sz <= MI_SMALL_SIZE_MAX`.
   The bound is also a safety condition, as a larger `sz` would index `pages_free_direct` out of
   bounds. Restating both lets the compiler fold the bin index into a plain byte offset and emit
   the `m_cs_sz` store below without a mask. */
static inline mi_page_t * lean_small_page(mi_theap_t * theap, unsigned sz) {
    lean_assert(sz > 0 && (sz % MI_INTPTR_SIZE) == 0 && sz <= MI_SMALL_SIZE_MAX);
#if defined(__GNUC__) || defined(__clang__)
    if ((sz % MI_INTPTR_SIZE) != 0 || sz == 0 || sz > MI_SMALL_SIZE_MAX) __builtin_unreachable();
#endif
    return _mi_theap_get_free_small_page(theap, sz);
}

/* Wraps mimalloc's generic allocation routine, out of line so that the entry point below can
   tail-jump here and stay a leaf function; a call that returned would cost it a prologue and
   epilogue on every allocation, to serve a path it almost never takes. Two things have to stay on
   this side for that to work: the OOM check, as only this routine can fail, and the `m_cs_sz`
   store, without which `sz` would have to survive the call. */
static mi_decl_noinline lean_object * lean_alloc_small_generic_core(mi_theap_t * theap, size_t sz) {
    void * mem = _mi_malloc_generic(theap, sz, 0, NULL);
    if (LEAN_UNLIKELY(mem == NULL)) lean_internal_panic_out_of_memory();
    lean_object * o = (lean_object *)mem;
    o->m_cs_sz = sz;
    return o;
}

extern "C" LEAN_EXPORT LEAN_ATTR_MALLOC lean_object * lean_alloc_small_object_core(unsigned sz) {
    lean_runtime_tls * tls = &lean_g_tls;
    tls->heartbeat++;
    lean_assert(sz > 0 && sz % LEAN_OBJECT_SIZE_DELTA == 0 && sz <= MI_SMALL_SIZE_MAX);
    /* Feeding the cached theap into mimalloc saves the load of mimalloc's own thread-local: the
       heartbeat update and the theap read share one TLS address computation. */
    mi_theap_t * const theap = tls->mi_theap_default;
    mi_page_t * const page = lean_small_page(theap, sz);
    if (LEAN_UNLIKELY(page->free == NULL)) return lean_alloc_small_generic_core(theap, sz);
    /* No OOM check: only the generic path can fail, and the test above diverts to it; see
       `lean_alloc_small_generic_core` for why the check belongs there. */
    lean_object * o = (lean_object *)mi_page_malloc_zero(theap, page, sz, false, NULL);
    /* `m_cs_sz` must be the exact (aligned) requested size, not mimalloc's potentially larger
       block size: `lean_small_object_size` and `leangz` rely on it. */
    o->m_cs_sz = sz;
    return o;
}
