/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <stdatomic.h>
#if !defined(__APPLE__)
#include <malloc.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

#ifdef _MSC_VER
#define LEAN_ALLOCA(s) _alloca(s)
#else
#define LEAN_ALLOCA(s) alloca(s)
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_UNLIKELY(x) (__builtin_expect((x), 0))
#define LEAN_LIKELY(x) (__builtin_expect((x), 1))
#define LEAN_ALWAYS_INLINE __attribute__((always_inline))
#else
#define LEAN_UNLIKELY(x) (x)
#define LEAN_LIKELY(x) (x)
#define LEAN_ALWAYS_INLINE
#endif

 #define LEAN_BYTE(Var, Index) *(((uint8_t*)&Var)+Index)

#define LeanMaxCtorTag  245
#define LeanClosure     246
#define LeanArray       247
#define LeanStructArray 248
#define LeanScalarArray 249
#define LeanString      250
#define LeanMPZ         251
#define LeanThunk       252
#define LeanTask        253
#define LeanRef         254
#define LeanExternal    255

#define LEAN_CASSERT(predicate) LEAN_impl_CASSERT_LINE(predicate, __LINE__, __FILE__)

#define LEAN_impl_PASTE(a, b) a##b
#define LEAN_impl_CASSERT_LINE(predicate, line, file) \
    typedef char LEAN_impl_PASTE(assertion_failed_##file##_, line)[2*!!(predicate)-1];

LEAN_CASSERT(sizeof(size_t) == sizeof(void*));

#ifdef LEAN_COMPRESSED_OBJECT_HEADER
// Compressed headers are only supported in 64-bit machines
LEAN_CASSERT(sizeof(void*) == 8);
#endif

/* Lean object header */
typedef struct {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    /* (high) 8-bits  : tag
              8-bits  : num fields for constructors, element size for scalar arrays
              1-bit   : single-threaded
              1-bit   : multi-threaded
              1-bit   : persistent
       (low)  45-bits : RC */
    _Atomic size_t m_header;
#define LEAN_PERSISTENT_BIT 45
#define LEAN_MT_BIT 46
#define LEAN_ST_BIT 47
#else
    _Atomic size_t m_rc;
    uint8_t        m_tag;
    uint8_t        m_mem_kind;
    uint16_t       m_other;  /* num fields for constructors, element size for scalar arrays, etc. */
#define LEAN_ST_MEM_KIND 0
#define LEAN_MT_MEM_KIND 1
#define LEAN_PERSISTENT_MEM_KIND 2
#define LEAN_OTHER_MEM_KIND 3
#endif
} lean_object;

/*
In our runtime, a Lean function consume the reference counter (RC) of its argument or not.
We say this behavior is part of the "calling convention" for the function. We say an argument uses:

1- "standard" calling convention if it consumes/decrements the RC.
   In this calling convention each argument should be viewed as a resource that is consumed by the function.
   This is roughly equivalent to `S && a` in C++, where `S` is a smart pointer, and `a` is the argument.
   When this calling convention is used for an argument `x`, then it is safe to perform destructive updates to
   `x` if its RC is 1.

2- "borrowed" calling convention if it doesn't consume/decrement the RC, and it is the responsability of the caller
   to decrement the RC.
   This is roughly equivalent to `S const & a` in C++, where `S` is a smart pointer, and `a` is the argument.

For returning objects, we also have two conventions

1- "standard" result. The caller is responsible for consuming the RC of the result.
   This is roughly equivalent to returning a smart point `S` by value in C++.

2- "borrowed" result. The caller is not responsible for decreasing the RC.
   This is roughly equivalent to returning a smart point reference `S const &` in C++.

Functions stored in closures use the "standard" calling convention.
*/

/* The following typedef's are used to document the calling convention for the primitives. */
typedef lean_object * lean_obj_arg;   /* Standard object argument. */
typedef lean_object * b_lean_obj_arg; /* Borrowed object argument. */
typedef lean_object * u_lean_obj_arg; /* Unique (aka non shared) object argument. */
typedef lean_object * lean_obj_res;   /* Standard object result. */
typedef lean_object * b_lean_obj_res; /* Borrowed object result. */

typedef struct {
    lean_object   m_header;
    lean_object * m_objs[0];
} lean_ctor_object;

/* Array arrays */
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    lean_object * m_data[0];
} lean_array_object;

/* Scalar arrays */
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    uint8_t       m_data[0];
} lean_sarray_object;

typedef struct {
    lean_object m_header;
    size_t      m_size;
    size_t      m_capacity;
    size_t      m_length;   // UTF8 length
    uint8_t     m_data[0];
} lean_string_object;

typedef struct {
    lean_object   m_header;
    void *        m_fun;
    uint16_t      m_arity;     // number of arguments expected by m_fun.
    uint16_t      m_num_fixed; // number of arguments that have been already fixed.
    lean_object * m_objs[0];
} lean_closure_object;

typedef struct {
    lean_object   m_header;
    lean_object * m_value;
} lean_ref_object;

typedef struct {
    lean_object           m_header;
    _Atomic lean_object * m_value;
    _Atomic lean_object * m_closure;
} lean_thunk_object;

struct lean_task;

/* Data required for executing a Lean task. It is released as soon as
   the task terminates. */
typedef struct {
    lean_object *        m_closure;
    struct lean_task *   m_head_dep;
    struct lean_task *   m_next_dep;
    unsigned             m_prio;
    uint8_t              m_interrupted;
    uint8_t              m_deleted;
} lean_task_imp;

typedef struct lean_task {
    lean_object           m_header;
    _Atomic lean_object * m_value;
    lean_task_imp *       m_imp;
} lean_task_object;

typedef void (*lean_external_finalize_proc)(void *);
typedef void (*lean_external_foreach_proc)(void *, b_lean_obj_arg);

typedef struct {
    lean_external_finalize_proc m_finalize;
    lean_external_foreach_proc  m_foreach;
} lean_external_class;

lean_external_class * lean_register_external_class(lean_external_finalize_proc, lean_external_foreach_proc);

/* Object for wrapping external data. */
typedef struct {
    lean_object         m_header;
    lean_external_class m_class;
    void *              m_data;
} lean_external_object;

static inline bool lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }
static inline lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
static inline size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }

void * lean_alloc_heap_object(size_t sz);
void lean_free_heap_obj(lean_object * o);

static inline bool lean_is_mt(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    return ((o->m_header >> LEAN_MT_BIT) & 1) != 0;
#else
    return o->m_mem_kind == LEAN_MT_MEM_KIND;
#endif
}

static inline bool lean_is_st(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    return ((o->m_header >> LEAN_ST_BIT) & 1) != 0;
#else
    return o->m_mem_kind == LEAN_ST_MEM_KIND;
#endif
}

static inline bool lean_is_heap_obj(lean_object * o) {
    return lean_is_st(o) || lean_is_mt(o);
}

static inline void lean_inc_ref(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_header++;
    } else if (lean_is_mt(o)) {
        atomic_fetch_add_explicit(&(o->m_header), 1, memory_order_relaxed);
    }
#else
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_rc++;
    } else if (lean_is_mt(o)) {
        atomic_fetch_add_explicit(&(o->m_rc), 1, memory_order_relaxed);
    }
#endif
}

static inline void lean_inc_ref_n(lean_object * o, size_t n) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_header += n;
    } else if (lean_is_mt(o)) {
        atomic_fetch_add_explicit(&(o->m_header), n, memory_order_relaxed);
    }
#else
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_rc += n;
    } else if (lean_is_mt(o)) {
        atomic_fetch_add_explicit(&(o->m_rc), n, memory_order_relaxed);
    }
#endif
}

static inline bool lean_dec_ref_core(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_header--;
        return ((o->m_header) & ((1ull << 45) - 1)) == 0;
    } else if (lean_is_mt(o)) {
        return (atomic_fetch_sub_explicit(&(o->m_header), 1, memory_order_acq_rel) & ((1ull << 45) - 1)) == 1;
    } else {
        return false;
    }
#else
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_rc--;
        return o->m_rc == 0;
    } else if (lean_is_mt(o)) {
        return atomic_fetch_sub_explicit(&(o->m_rc), 1, memory_order_acq_rel) == 1;
    } else {
        return false;
    }
#endif
}

/* Generic Lean object delete operation. */
void lean_del(lean_object * o);

static inline void lean_dec_ref(lean_object * o) { if (lean_dec_ref_core(o)) lean_del(o); }
static inline void lean_inc(lean_object * o) { if (!lean_is_scalar(o)) lean_inc_ref(o); }
static inline void lean_inc_n(lean_object * o, size_t n) { if (!lean_is_scalar(o)) lean_inc_ref_n(o, n); }
static inline void lean_dec(lean_object * o) { if (!lean_is_scalar(o)) lean_dec_ref(o); }

/* Just free memory */
void lean_dealloc(lean_object * o);

static inline uint8_t lean_ptr_tag(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    return LEAN_BYTE(o->m_header, 7);
#else
    return o->m_tag;
#endif
}

static inline bool lean_is_ctor(lean_object * o) { return lean_ptr_tag(o) <= LeanMaxCtorTag; }
static inline bool lean_is_closure(lean_object * o) { return lean_ptr_tag(o) == LeanClosure; }
static inline bool lean_is_array(lean_object * o) { return lean_ptr_tag(o) == LeanArray; }
static inline bool lean_is_sarray(lean_object * o) { return lean_ptr_tag(o) == LeanScalarArray; }
static inline bool lean_is_string(lean_object * o) { return lean_ptr_tag(o) == LeanString; }
static inline bool lean_is_mpz(lean_object * o) { return lean_ptr_tag(o) == LeanMPZ; }
static inline bool lean_is_thunk(lean_object * o) { return lean_ptr_tag(o) == LeanThunk; }
static inline bool lean_is_task(lean_object * o) { return lean_ptr_tag(o) == LeanTask; }
static inline bool lean_is_external(lean_object * o) { return lean_ptr_tag(o) == LeanExternal; }
static inline bool lean_is_ref(lean_object * o) { return lean_ptr_tag(o) == LeanRef; }

static inline unsigned lean_obj_tag(lean_object * o) {
    if (lean_is_scalar(o)) return lean_unbox(o); else return lean_ptr_tag(o);
}

static inline lean_ctor_object * lean_to_ctor(lean_object * o) { assert(lean_is_ctor(o)); return (lean_ctor_object*)(o); }
static inline lean_closure_object * lean_to_closure(lean_object * o) { assert(lean_is_closure(o)); return (lean_closure_object*)(o); }
static inline lean_array_object * lean_to_array(lean_object * o) { assert(lean_is_array(o)); return (lean_array_object*)(o); }
static inline lean_sarray_object * lean_to_sarray(lean_object * o) { assert(lean_is_sarray(o)); return (lean_sarray_object*)(o); }
static inline lean_string_object * lean_to_string(lean_object * o) { assert(lean_is_string(o)); return (lean_string_object*)(o); }
static inline lean_thunk_object * lean_to_thunk(lean_object * o) { assert(lean_is_thunk(o)); return (lean_thunk_object*)(o); }
static inline lean_task_object * lean_to_task(lean_object * o) { assert(lean_is_task(o)); return (lean_task_object*)(o); }
static inline lean_ref_object * lean_to_ref(lean_object * o) { assert(lean_is_ref(o)); return (lean_ref_object*)(o); }
static inline lean_external_object * lean_to_external(lean_object * o) { assert(lean_is_external(o)); return (lean_external_object*)(o); }

static inline bool lean_is_exclusive(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    if (LEAN_LIKELY(lean_is_st(o))) {
        return ((o->m_header) & ((1ull << 45) - 1)) == 1;
    } else if (lean_is_mt(o)) {
        return (atomic_load_explicit(&(o->m_header), memory_order_acquire) & ((1ull << 45) - 1)) == 1;
    } else {
        return false;
    }
#else
    if (LEAN_LIKELY(lean_is_st(o))) {
        return o->m_rc == 1;
    } else if (lean_is_mt(o)) {
        return atomic_load_explicit(&(o->m_rc), memory_order_acquire) == 1;
    } else {
        return false;
    }
#endif
}

static inline bool lean_is_shared(lean_object * o) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    if (LEAN_LIKELY(lean_is_st(o))) {
        return ((o->m_header) & ((1ull << 45) - 1)) > 1;
    } else if (lean_is_mt(o)) {
        return (atomic_load_explicit(&(o->m_header), memory_order_acquire) & ((1ull << 45) - 1)) > 1;
    } else {
        return false;
    }
#else
    if (LEAN_LIKELY(lean_is_st(o))) {
        return o->m_rc > 1;
    } else if (lean_is_mt(o)) {
        return atomic_load_explicit(&(o->m_rc), memory_order_acquire) > 1;
    } else {
        return false;
    }
#endif
}

void lean_mark_mt(lean_object * o);
void lean_mark_persistent(lean_object * o);

static inline void lean_set_header(lean_object * o, unsigned tag, unsigned other) {
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    o->m_header   = ((size_t)(tag) << 56) | ((size_t)(other) << 48) | (1ull << LEAN_ST_BIT) | 1;
#else
    o->m_rc       = 1;
    o->m_tag      = tag;
    o->m_mem_kind = LEAN_ST_MEM_KIND;
    o->m_other    = other;
#endif
}

/* Constructor objects */

static inline unsigned lean_ctor_num_objs(lean_object * o) {
    assert(lean_is_ctor(o));
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    return LEAN_BYTE(o->m_header, 6);
#else
    return o->m_other;
#endif
}

static inline lean_object ** lean_ctor_obj_cptr(lean_object * o) {
    assert(lean_is_ctor(o));
    return lean_to_ctor(o)->m_objs;
}

static inline uint8_t * lean_ctor_scalar_cptr(lean_object * o) {
    assert(lean_is_ctor(o));
    return (uint8_t*)(lean_ctor_obj_cptr(o) + lean_ctor_num_objs(o));
}

static inline lean_object * lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    assert(tag <= LeanMaxCtorTag && num_objs < 256 && scalar_sz < 1024);
    lean_object * o = (lean_object*)lean_alloc_heap_object(sizeof(lean_ctor_object) + sizeof(void*)*num_objs + scalar_sz);
    lean_set_header(o, tag, num_objs);
    return o;
}

static inline b_lean_obj_res lean_ctor_get(b_lean_obj_arg o, unsigned i) {
    assert(i < lean_ctor_num_objs(o));
    return lean_ctor_obj_cptr(o)[i];
}

static inline void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v) {
    assert(i < lean_ctor_num_objs(o));
    lean_ctor_obj_cptr(o)[i] = v;
}

static inline void lean_ctor_set_tag(b_lean_obj_arg o, uint8_t new_tag) {
    assert(new_tag <= LeanMaxCtorTag);
#ifdef LEAN_COMPRESSED_OBJECT_HEADER
    LEAN_BYTE(o->m_header, 7) = new_tag;
#else
    o->m_tag = new_tag;
#endif
}

static inline void lean_ctor_release(b_lean_obj_arg o, unsigned i) {
    assert(i < lean_ctor_num_objs(o));
    lean_object ** objs = lean_ctor_obj_cptr(o);
    lean_dec(objs[i]);
    objs[i] = lean_box(0);
}

static inline size_t lean_ctor_usize(b_lean_obj_arg o, unsigned i) {
    assert(i >= lean_ctor_num_objs(o));
    return *((size_t*)(lean_ctor_obj_cptr(o) + i));
}

static inline uint8_t lean_ctor_get_uint8(b_lean_obj_arg o, unsigned offset) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    return *((uint8_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));
}

static inline uint16_t lean_ctor_get_uint16(b_lean_obj_arg o, unsigned offset) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    return *((uint16_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));
}

static inline uint32_t lean_ctor_get_uint32(b_lean_obj_arg o, unsigned offset) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    return *((uint32_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));
}

static inline uint64_t lean_ctor_get_uint64(b_lean_obj_arg o, unsigned offset) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    return *((uint64_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));
}

static inline void lean_ctor_set_usize(b_lean_obj_arg o, unsigned i, size_t v) {
    assert(i >= lean_ctor_num_objs(o));
    *((size_t*)(lean_ctor_obj_cptr(o) + i)) = v;
}

static inline void lean_ctor_set_uint8(b_lean_obj_arg o, unsigned offset, uint8_t v) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    *((uint8_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;
}

static inline void lean_ctor_set_uint16(b_lean_obj_arg o, unsigned offset, uint16_t v) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    *((uint16_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;
}

static inline void lean_ctor_set_uint32(b_lean_obj_arg o, unsigned offset, uint32_t v) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    *((uint32_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;
}

static inline void lean_ctor_set_uint64(b_lean_obj_arg o, unsigned offset, uint64_t v) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    *((uint64_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;
}

/* Closures */

inline void * lean_closure_fun(lean_object * o) { return lean_to_closure(o)->m_fun; }
inline unsigned lean_closure_arity(lean_object * o) { return lean_to_closure(o)->m_arity; }
inline unsigned lean_closure_num_fixed(lean_object * o) { return lean_to_closure(o)->m_num_fixed; }
inline lean_object ** lean_closure_arg_cptr(lean_object * o) { return lean_to_closure(o)->m_objs; }
inline lean_obj_res lean_alloc_closure(void * fun, unsigned arity, unsigned num_fixed) {
    assert(arity > 0);
    assert(num_fixed < arity);
    lean_closure_object * o = (lean_closure_object*)lean_alloc_heap_object(sizeof(lean_closure_object) + sizeof(void*)*num_fixed);
    lean_set_header((lean_object*)o, LeanClosure, 0);
    o->m_fun = fun;
    o->m_arity = arity;
    o->m_num_fixed = num_fixed;
    return (lean_object*)o;
}
inline b_lean_obj_res lean_closure_get(b_lean_obj_arg o, unsigned i) {
    assert(i < lean_closure_num_fixed(o));
    return lean_to_closure(o)->m_objs[i];
}
inline void lean_closure_set(u_lean_obj_arg o, unsigned i, lean_obj_arg a) {
    assert(i < lean_closure_num_fixed(o));
    lean_to_closure(o)->m_objs[i] = a;
}

/* Fixpoint */

lean_obj_res lean_fixpoint(lean_obj_arg rec, lean_obj_arg a);
lean_obj_res lean_fixpoint2(lean_obj_arg rec, lean_obj_arg a1, lean_obj_arg a2);
lean_obj_res lean_fixpoint3(lean_obj_arg rec, lean_obj_arg a1, lean_obj_arg a2, lean_obj_arg a3);
lean_obj_res lean_fixpoint4(lean_obj_arg rec, lean_obj_arg a1, lean_obj_arg a2, lean_obj_arg a3, lean_obj_arg a4);
lean_obj_res lean_fixpoint5(lean_obj_arg rec, lean_obj_arg a1, lean_obj_arg a2, lean_obj_arg a3, lean_obj_arg a4, lean_obj_arg a5);
lean_obj_res lean_fixpoint6(lean_obj_arg rec, lean_obj_arg a1, lean_obj_arg a2, lean_obj_arg a3, lean_obj_arg a4, lean_obj_arg a5, lean_obj_arg a6);

#ifdef __cplusplus
}
#endif
