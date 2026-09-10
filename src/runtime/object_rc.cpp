/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/
/*
Allocation and deletion entry points driven by reference counting. With mimalloc enabled this file
is not compiled on its own but #included into `mimalloc.cpp`, so that mimalloc's `mi_malloc` and
`mi_free` fast paths inline into `lean_alloc_object` and the deletion loop (`lean_del_core`);
without mimalloc it is compiled as an ordinary translation unit.
*/
#include <atomic>
#include <cstring>
#include <lean/lean.h>
#include "runtime/object.h"
#include "runtime/thread.h"

namespace lean {

/* Defined in `object.cpp`. */
void deactivate_task(lean_task_object * t);
void deactivate_promise(lean_promise_object * t);

extern "C" LEAN_EXPORT void lean_free_object(lean_object * o) {
    switch (lean_ptr_tag(o)) {
    case LeanArray:       return lean_dealloc(o, lean_array_byte_size(o));
    case LeanScalarArray: return lean_dealloc(o, lean_sarray_byte_size(o));
    case LeanString:      return lean_dealloc(o, lean_string_byte_size(o));
    case LeanClosure:     return lean_dealloc(o, lean_closure_byte_size(o));
    case LeanMPZ:         to_mpz(o)->m_value.~mpz(); return lean_free_small_object(o);
    default:              return lean_free_small_object(o);
    }
}

static inline lean_object * get_next(lean_object * o) {
    if (sizeof(void*) == 8) {
        size_t header = ((size_t*)o)[0];
        LEAN_BYTE(header, 7) = 0;
        LEAN_BYTE(header, 6) = 0;
        return (lean_object*)(header);
    } else {
        // 32-bit version
        return ((lean_object**)o)[0];
    }
}

// See the docstring on `lean_object*` for details about pointer packing.
#if defined(__has_feature)
    #if __has_feature(hwaddress_sanitizer)
        #define LEAN_HAS_HWASAN 1
    #endif
#endif
#if defined(LEAN_HAS_HWASAN) || defined(__SANITIZE_HWADDRESS__) || \
    defined(__ARM_FEATURE_MEMORY_TAGGING)
    #define LEAN_PTR_PACKING_SAFE false
#else
    #define LEAN_PTR_PACKING_SAFE true
#endif

static_assert(sizeof(void*) != 8 || LEAN_PTR_PACKING_SAFE,
    "Cannot compile with HWASAN or ARM MTE enabled; on 64-bit machines, "
    "the pointer packing in `set_next` truncates the top byte used by these features.\n"
    "See https://github.com/leanprover/lean4/issues/13113.");

static inline void set_next(lean_object * o, lean_object * n) {
    if (sizeof(void*) == 8) {
        uint16_t hi;
        memcpy(&hi, (char*)o + 6, 2);
        size_t header = ((size_t)hi << 48) | (size_t)n;
        memcpy(o, &header, 8);
    } else {
        // 32-bit version
        ((lean_object**)o)[0] = n;
    }
}

static inline void push_back(lean_object * & todo, lean_object * v) {
    set_next(v, todo);
    todo = v;
}

static inline lean_object * pop_back(lean_object * & todo) {
    lean_object * r = todo;
    todo = get_next(todo);
    return r;
}

static inline void dec(lean_object * o, lean_object* & todo) {
    if (lean_is_scalar(o))
        return;
    if (LEAN_LIKELY(lean_internal_get_rc(o) > 1)) {
        lean_internal_sub_rc(o, 1);
    } else if (lean_internal_get_rc(o) == 1) {
        push_back(todo, o);
    } else if (lean_internal_get_rc(o) == 0) {
        return;
    } else if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_acq_rel) == -1) {
        push_back(todo, o);
    }
}

extern "C" LEAN_EXPORT lean_object * lean_alloc_object(size_t sz) {
#ifdef LEAN_MIMALLOC
    void * r = mi_malloc(sz);
    if (r == nullptr) lean_internal_panic_out_of_memory();
    lean_object * o = (lean_object*)r;
    // not a small object
    o->m_cs_sz = 0;
    return o;
#else
    void * r = malloc(sz);
    if (r == nullptr) lean_internal_panic_out_of_memory();
    return (lean_object*)r;
#endif
}

/* The deletion worklist is passed by value and returned rather than by reference so that it can
   live in a register across the constructor loop, which is by far the hottest deletion path. */
static object * lean_del_core_other(object * o, uint8 tag, object * todo) {
    switch (tag) {
    case LeanClosure: {
        object ** it  = lean_closure_arg_cptr(o);
        object ** end = it + lean_closure_num_fixed(o);
        for (; it != end; ++it) dec(*it, todo);
        lean_dealloc(o, lean_closure_byte_size(o));
        break;
    }
    case LeanArray: {
        object ** it  = lean_array_cptr(o);
        object ** end = it + lean_array_size(o);
        for (; it != end; ++it) dec(*it, todo);
        lean_dealloc(o, lean_array_byte_size(o));
        break;
    }
    case LeanScalarArray:
        lean_dealloc(o, lean_sarray_byte_size(o));
        break;
    case LeanString:
        lean_dealloc(o, lean_string_byte_size(o));
        break;
    case LeanMPZ:
        to_mpz(o)->m_value.~mpz();
        lean_free_small_object(o);
        break;
    case LeanThunk:
        if (object * c = lean_to_thunk(o)->m_closure) dec(c, todo);
        if (object * v = lean_to_thunk(o)->m_value) dec(v, todo);
        lean_free_small_object(o);
        break;
    case LeanRef:
        if (object * v = lean_to_ref(o)->m_value) dec(v, todo);
        lean_free_small_object(o);
        break;
    case LeanTask:
        deactivate_task(lean_to_task(o));
        break;
    case LeanPromise:
        deactivate_promise(lean_to_promise(o));
        break;
    case LeanExternal:
        lean_to_external(o)->m_class->m_finalize(lean_to_external(o)->m_data);
        lean_free_small_object(o);
        break;
    default:
        lean_unreachable();
    }
    return todo;
}

static object * lean_del_core(object * o, object * todo) {
    uint8 tag = lean_ptr_tag(o);
    if (LEAN_LIKELY(tag <= LeanMaxCtorTag)) {
        object ** it  = lean_ctor_obj_cptr(o);
        object ** end = it + lean_ctor_num_objs(o);
        for (; it != end; ++it) dec(*it, todo);
        lean_free_small_object(o);
        return todo;
    } else {
        return lean_del_core_other(o, tag, todo);
    }
}

// sync with tests/elab/rc_sticky_thresholds.lean (`incRefHugeN`)
extern "C" LEAN_EXPORT void lean_inc_ref_huge_n(lean_object * o, size_t n) {
    // `n` is above what `lean_inc_ref_n` adjusts by inline. Only `lean_mk_array` gets here.
    if (lean_is_st(o)) {
        int rc = lean_internal_get_rc(o);
        if (n > (size_t)(INT_MAX - rc))
            lean_internal_set_rc(o, LEAN_RC_STICKY);
        else
            lean_internal_set_rc(o, rc + (int)n);
    } else {
        // The loop condition is the sticky test `lean_inc_ref_n` makes before its own
        // `fetch_sub`, so each iteration is one ordinary increment of at most `LEAN_RC_INC_MAX`,
        // and re-reading the count stops the loop once the count freezes.
        while (n > 0 && (unsigned)lean_internal_get_rc(o) > (unsigned)LEAN_RC_STICKY) {
            size_t chunk = std::min(n, LEAN_RC_INC_MAX);
            std::atomic_fetch_sub_explicit(lean_get_rc_mt_addr(o), (int)chunk,
                                           std::memory_order_relaxed);
            n -= chunk;
        }
    }
}

// sync with tests/elab/rc_sticky_thresholds.lean (`decRefCold`)
extern "C" LEAN_EXPORT void lean_dec_ref_cold(lean_object * o) {
    // `rc == 1` is the hot single-threaded free path and can never be sticky, so the sticky check
    // is kept out of it.
    if (lean_internal_get_rc(o) != 1) {
        if (LEAN_UNLIKELY(lean_internal_get_rc(o) <= LEAN_RC_STICKY_DROP))
            return; // over- or underflowed (sticky) count: never adjust or free
        if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1, std::memory_order_acq_rel) != -1)
            return;
    }
    object * todo = nullptr;
    while (true) {
        todo = lean_del_core(o, todo);
        if (todo == nullptr)
            return;
        o = pop_back(todo);
    }
}

}
