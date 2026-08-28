/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/
/*
Compiles all of mimalloc (`static.c`) together with the runtime's small-object allocation entry
points in a single translation unit so that mimalloc's allocation fast path inlines into them:
compiled Lean code reaches the allocator, including the heartbeat update, with a single call.
`static.c` must come first so that mimalloc's headers configure themselves from this variant's
`MI_*` flags (see `add_mimalloc_variant` in `CMakeLists.txt`) before `lean/mimalloc.h` is seen.
*/
#include <static.c>
// mimalloc's `atomic.h` already defined `_Atomic` for C++; `lean.h` redefines it identically
#undef _Atomic
#include <lean/lean.h>
#include "runtime/alloc.h"

extern "C" LEAN_EXPORT LEAN_ATTR_MALLOC lean_object * lean_alloc_small_object_core(unsigned sz) {
    lean_g_heartbeat++;
    /* The callers guarantee `sz <= MI_SMALL_SIZE_MAX`, so `mi_malloc_small` applies; unlike
       `mi_malloc` it does not have to test the size on the fast path. */
    void * mem = mi_malloc_small(sz);
    if (LEAN_UNLIKELY(mem == NULL)) lean_internal_panic_out_of_memory();
    lean_object * o = (lean_object *)mem;
    /* `m_cs_sz` must be the exact (aligned) requested size, not mimalloc's potentially larger
       block size: `lean_small_object_size` and `leangz` rely on it. */
    o->m_cs_sz = sz;
    return o;
}

extern "C" LEAN_EXPORT LEAN_ATTR_MALLOC lean_object * lean_alloc_small_object_raw(unsigned sz) {
    lean_g_heartbeat++;
    void * mem = mi_malloc_small(sz);
    if (LEAN_UNLIKELY(mem == NULL)) lean_internal_panic_out_of_memory();
    /* The caller initializes the entire header, including `m_cs_sz`; leaving it out here keeps
       `sz` dead after the allocation, so this compiles to a minimal leaf-like fast path. */
    return (lean_object *)mem;
}

/* Big-object allocation and the RC deletion machinery, in this TU for the same reason as the
   entry points above: `mi_malloc`/`mi_free` inline into them. */
#include "object_rc.cpp"
