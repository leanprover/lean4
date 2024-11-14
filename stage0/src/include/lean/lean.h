/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <limits.h>

#ifdef __cplusplus
#include <atomic>
#include <stdlib.h>
#define _Atomic(t) std::atomic<t>
#define LEAN_USING_STD using namespace std; /* NOLINT */
extern "C" {
#else
#define  LEAN_USING_STD
#endif
#include <lean/config.h>

#define LEAN_CLOSURE_MAX_ARGS      16
#define LEAN_OBJECT_SIZE_DELTA     8
#define LEAN_MAX_SMALL_OBJECT_SIZE 4096

#ifdef _MSC_VER
#define LEAN_ALLOCA(s) _alloca(s)
#include <stdnoreturn.h>
#define LEAN_NORETURN _Noreturn
#else
#define LEAN_ALLOCA(s) alloca(s)
#define LEAN_NORETURN __attribute__((noreturn))
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

#ifndef assert
#ifdef NDEBUG
#define assert(expr)
#else
void lean_notify_assert(const char * fileName, int line, const char * condition);
#define assert(expr) { if (LEAN_UNLIKELY(!(expr))) lean_notify_assert(__FILE__, __LINE__, #expr); }
#endif
#endif

// We set `LEAN_EXPORTING` when compiling objects of libleanshared, but not when including this header in any other context.
#ifdef LEAN_EXPORTING
#ifdef _WIN32
#define LEAN_EXPORT __declspec(dllexport)
#else
#define LEAN_EXPORT __attribute__((visibility("default")))
#endif
#else
#define LEAN_EXPORT
#endif

#define LEAN_BYTE(Var, Index) *(((uint8_t*)&Var)+Index)

#define LeanMaxCtorTag  244
#define LeanClosure     245
#define LeanArray       246
#define LeanStructArray 247
#define LeanScalarArray 248
#define LeanString      249
#define LeanMPZ         250
#define LeanThunk       251
#define LeanTask        252
#define LeanRef         253
#define LeanExternal    254
#define LeanReserved    255

#define LEAN_MAX_CTOR_FIELDS 256
#define LEAN_MAX_CTOR_SCALARS_SIZE 1024

static inline bool lean_is_big_object_tag(uint8_t tag) {
    return tag == LeanArray || tag == LeanStructArray || tag == LeanScalarArray || tag == LeanString;
}

#define LEAN_CASSERT(predicate) LEAN_impl_CASSERT_LINE(predicate, __LINE__, __FILE__)

#define LEAN_impl_PASTE(a, b) a##b
#define LEAN_impl_CASSERT_LINE(predicate, line, file) \
    typedef char LEAN_impl_PASTE(assertion_failed_##file##_, line)[2*!!(predicate)-1];

LEAN_CASSERT(sizeof(size_t) == sizeof(void*));

/*
Lean object header.

The reference counter `m_rc` field also encodes whether the object is single threaded (> 0), multi threaded (< 0), or
reference counting is not needed (== 0). We don't use reference counting for objects stored in compact regions, or
marked as persistent.

For "small" objects stored in compact regions, the field `m_cs_sz` contains the object size. For "small" objects not
stored in compact regions, we use the page information to retrieve its size.

During deallocation and 64-bit machines, the fields `m_rc` and `m_cs_sz` store the next object in the deletion TODO list.
These two fields together have 48-bits, and this is enough for modern computers.
In 32-bit machines, the field `m_rc` is sufficient.

The field `m_other` is used to store the number of fields in a constructor object and the element size in a scalar array.
*/
typedef struct {
    int      m_rc;
    unsigned m_cs_sz:16;
    unsigned m_other:8;
    unsigned m_tag:8;
} lean_object;

/*
In our runtime, a Lean function consume the reference counter (RC) of its argument or not.
We say this behavior is part of the "calling convention" for the function. We say an argument uses:
x
1- "standard" calling convention if it consumes/decrements the RC.
   In this calling convention each argument should be viewed as a resource that is consumed by the function.
   This is roughly equivalent to `S && a` in C++, where `S` is a smart pointer, and `a` is the argument.
   When this calling convention is used for an argument `x`, then it is safe to perform destructive updates to
   `x` if its RC is 1.

2- "borrowed" calling convention if it doesn't consume/decrement the RC, and it is the responsibility of the caller
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
    lean_object * m_objs[];
} lean_ctor_object;

/* Array arrays */
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    lean_object * m_data[];
} lean_array_object;

/* Scalar arrays */
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    uint8_t       m_data[];
} lean_sarray_object;

typedef struct {
    lean_object m_header;
    size_t      m_size;     /* byte length including '\0' terminator */
    size_t      m_capacity;
    size_t      m_length;   /* UTF8 length */
    char        m_data[];
} lean_string_object;

typedef struct {
    lean_object   m_header;
    void *        m_fun;
    uint16_t      m_arity;     /* Number of arguments expected by m_fun. */
    uint16_t      m_num_fixed; /* Number of arguments that have been already fixed. */
    lean_object * m_objs[];
} lean_closure_object;

typedef struct {
    lean_object   m_header;
    lean_object * m_value;
} lean_ref_object;

typedef struct {
    lean_object            m_header;
    _Atomic(lean_object *) m_value;
    _Atomic(lean_object *) m_closure;
} lean_thunk_object;

struct lean_task;

/* Data required for executing a Lean task. It is released as soon as
   the task terminates even if the task object itself is still referenced. */
typedef struct {
    lean_object *        m_closure;
    struct lean_task *   m_head_dep;
    struct lean_task *   m_next_dep;
    unsigned             m_prio;
    uint8_t              m_canceled;
    // If true, task will not be freed until finished
    uint8_t              m_keep_alive;
    uint8_t              m_deleted;
} lean_task_imp;

/* Object of type `Task _`. The lifetime of a `lean_task` object can be represented as a state machine with atomic
   state transitions.

   In the following, `condition` describes a predicate uniquely identifying a state.

   creation:
   * Task.spawn ==> Queued
   * Task.map/bind ==> Waiting
   * Task.pure ==> Finished
   * Promise.new ==> Promised

   states:
   * Queued
     * condition: in task_manager::m_queues && m_imp != nullptr && !m_imp->m_deleted
     * invariant: m_value == nullptr
     * transition: RC becomes 0 ==> Deactivated (`deactivate_task` lock)
     * transition: dequeued by worker thread            ==> Running     (`spawn_worker` lock)
   * Waiting
     * condition: reachable from task via `m_head_dep->m_next_dep->...` && !m_imp->m_deleted
     * invariant: m_imp != nullptr && m_value == nullptr
     * invariant: task dependency is Queued/Waiting/Running
       * It cannot become Deactivated because this task should be holding an owned reference to it
     * transition: RC becomes 0 ==> Deactivated (`deactivate_task` lock)
     * transition: task dependency Finished ==> Queued (`handle_finished` under `spawn_worker` lock)
   * Promised
     * condition: obtained as result from promise
     * invariant: m_imp != nullptr && m_value == nullptr
     * transition: promise resolved ==> Finished (`resolve_core` under `spawn_worker` lock)
     * transition: RC becomes 0 ==> Deactivated (`deactivate_task` lock)
   * Running
     * condition: m_imp != nullptr && m_imp->m_closure == nullptr
       * The worker takes ownership of the closure when running it
     * invariant: m_value == nullptr
     * transition: RC becomes 0 ==> Deactivated (`deactivate_task` lock)
     * transition: finished execution                   ==> Finished    (`spawn_worker` lock)
   * Deactivated
     * condition: m_imp != nullptr && m_imp->m_deleted
     * invariant: RC == 0
     * invariant: m_imp->m_closure == nullptr && m_imp->m_head_dep == nullptr (both freed by `deactivate_task_core`)
       * Note that all dependent tasks must have already been Deactivated by the converse of the second Waiting invariant
     * invariant: m_value == nullptr
     * transition: dequeued by worker thread   ==> freed
     * transition: finished execution          ==> freed
     * transition: task dependency Finished    ==> freed
     * We must keep the task object alive until one of these transitions because in either case, we have live
       (internal, unowned) references to the task up to that point
     * transition: task dependency Deactivated ==> freed
   * Finished
     * condition: m_value != nullptr
     * invariant: m_imp == nullptr
     * transition: RC becomes 0 ==> freed (`deactivate_task` lock) */
typedef struct lean_task {
    lean_object            m_header;
    _Atomic(lean_object *) m_value;
    lean_task_imp *        m_imp;
} lean_task_object;

typedef void (*lean_external_finalize_proc)(void *);
typedef void (*lean_external_foreach_proc)(void *, b_lean_obj_arg);

typedef struct {
    lean_external_finalize_proc m_finalize;
    lean_external_foreach_proc  m_foreach;
} lean_external_class;

LEAN_EXPORT lean_external_class * lean_register_external_class(lean_external_finalize_proc, lean_external_foreach_proc);

/* Object for wrapping external data. */
typedef struct {
    lean_object           m_header;
    lean_external_class * m_class;
    void *                m_data;
} lean_external_object;

static inline bool lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }
static inline lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
static inline size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }

LEAN_EXPORT void lean_set_exit_on_panic(bool flag);
/* Enable/disable panic messages */
LEAN_EXPORT void lean_set_panic_messages(bool flag);

LEAN_EXPORT lean_object * lean_panic_fn(lean_object * default_val, lean_object * msg);

LEAN_EXPORT LEAN_NORETURN void lean_internal_panic(char const * msg);
LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_out_of_memory(void);
LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_unreachable(void);
LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_rc_overflow(void);

static inline size_t lean_align(size_t v, size_t a) {
    return (v / a)*a + a * (v % a != 0);
}

static inline unsigned lean_get_slot_idx(unsigned sz) {
    assert(sz > 0);
    assert(lean_align(sz, LEAN_OBJECT_SIZE_DELTA) == sz);
    return sz / LEAN_OBJECT_SIZE_DELTA - 1;
}

LEAN_EXPORT void * lean_alloc_small(unsigned sz, unsigned slot_idx);
LEAN_EXPORT void lean_free_small(void * p);
LEAN_EXPORT unsigned lean_small_mem_size(void * p);
LEAN_EXPORT void lean_inc_heartbeat(void);

#ifndef __cplusplus
void * malloc(size_t);  // avoid including big `stdlib.h`
#endif

static inline lean_object * lean_alloc_small_object(unsigned sz) {
#ifdef LEAN_SMALL_ALLOCATOR
    sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
    unsigned slot_idx = lean_get_slot_idx(sz);
    assert(sz <= LEAN_MAX_SMALL_OBJECT_SIZE);
    return (lean_object*)lean_alloc_small(sz, slot_idx);
#else
    lean_inc_heartbeat();
    void * mem = malloc(sizeof(size_t) + sz);
    if (mem == 0) lean_internal_panic_out_of_memory();
    *(size_t*)mem = sz;
    return (lean_object*)((size_t*)mem + 1);
#endif
}

static inline lean_object * lean_alloc_ctor_memory(unsigned sz) {
#ifdef LEAN_SMALL_ALLOCATOR
    unsigned sz1 = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
    unsigned slot_idx = lean_get_slot_idx(sz1);
    assert(sz1 <= LEAN_MAX_SMALL_OBJECT_SIZE);
    lean_object* r = (lean_object*)lean_alloc_small(sz1, slot_idx);
    if (sz1 > sz) {
        /* Initialize last word.
           In our runtime `lean_object_byte_size` is always
           a multiple of the machine word size for constructors.

           By setting the last word to 0, we make sure the sharing
           maximizer procedures at `maxsharing.cpp` and `compact.cpp` are
           not affected by uninitialized data at the (sz1 - sz) last bytes.
           Otherwise, we may mistakenly assume to structurally equal
           objects are not identical because of this uninitialized memory. */
        size_t * end = (size_t*)(((char*)r) + sz1);
        end[-1] = 0;
    }
    return r;
#else
    return lean_alloc_small_object(sz);
#endif
}

static inline unsigned lean_small_object_size(lean_object * o) {
#ifdef LEAN_SMALL_ALLOCATOR
    return lean_small_mem_size(o);
#else
    return *((size_t*)o - 1);
#endif
}

#ifndef __cplusplus
void free(void *);  // avoid including big `stdlib.h`
#endif

static inline void lean_free_small_object(lean_object * o) {
#ifdef LEAN_SMALL_ALLOCATOR
    lean_free_small(o);
#else
    free((size_t*)o - 1);
#endif
}

LEAN_EXPORT lean_object * lean_alloc_object(size_t sz);
LEAN_EXPORT void lean_free_object(lean_object * o);

static inline uint8_t lean_ptr_tag(lean_object * o) {
    return o->m_tag;
}

static inline unsigned lean_ptr_other(lean_object * o) {
    return o->m_other;
}

/* The object size may be slightly bigger for constructor objects.
   The runtime does not track the size of the scalar size area.
   All constructor objects are "small", and allocated into pages.
   We retrieve their size by accessing the page header. The size of
   small objects is a multiple of LEAN_OBJECT_SIZE_DELTA */
LEAN_EXPORT size_t lean_object_byte_size(lean_object * o);

static inline bool lean_is_mt(lean_object * o) {
    return o->m_rc < 0;
}

static inline bool lean_is_st(lean_object * o) {
    return o->m_rc > 0;
}

/* We never update the reference counter of objects stored in compact regions and allocated at initialization time. */
static inline bool lean_is_persistent(lean_object * o) {
    return o->m_rc == 0;
}

static inline bool lean_has_rc(lean_object * o) {
    return o->m_rc != 0;
}

static inline _Atomic(int) * lean_get_rc_mt_addr(lean_object* o) {
    return (_Atomic(int)*)(&(o->m_rc));
}

LEAN_EXPORT void lean_inc_ref_cold(lean_object * o);
LEAN_EXPORT void lean_inc_ref_n_cold(lean_object * o, unsigned n);

static inline void lean_inc_ref(lean_object * o) {
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_rc++;
    } else if (o->m_rc != 0) {
        lean_inc_ref_cold(o);
    }
}

static inline void lean_inc_ref_n(lean_object * o, size_t n) {
    if (LEAN_LIKELY(lean_is_st(o))) {
        o->m_rc += n;
    } else if (o->m_rc != 0) {
        lean_inc_ref_n_cold(o, n);
    }
}

LEAN_EXPORT void lean_dec_ref_cold(lean_object * o);

static inline void lean_dec_ref(lean_object * o) {
    if (LEAN_LIKELY(o->m_rc > 1)) {
        o->m_rc--;
    } else if (o->m_rc != 0) {
        lean_dec_ref_cold(o);
    }
}
static inline void lean_inc(lean_object * o) { if (!lean_is_scalar(o)) lean_inc_ref(o); }
static inline void lean_inc_n(lean_object * o, size_t n) { if (!lean_is_scalar(o)) lean_inc_ref_n(o, n); }
static inline void lean_dec(lean_object * o) { if (!lean_is_scalar(o)) lean_dec_ref(o); }

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
    if (LEAN_LIKELY(lean_is_st(o))) {
        return o->m_rc == 1;
    } else {
        return false;
    }
}

static inline uint8_t lean_is_exclusive_obj(lean_object * o) {
    return lean_is_exclusive(o);
}

static inline bool lean_is_shared(lean_object * o) {
    if (LEAN_LIKELY(lean_is_st(o))) {
        return o->m_rc > 1;
    } else {
        return false;
    }
}

LEAN_EXPORT void lean_mark_mt(lean_object * o);
LEAN_EXPORT void lean_mark_persistent(lean_object * o);

static inline void lean_set_st_header(lean_object * o, unsigned tag, unsigned other) {
    o->m_rc       = 1;
    o->m_tag      = tag;
    o->m_other    = other;
    o->m_cs_sz    = 0;
}

/* Remark: we don't need a reference counter for objects that are not stored in the heap.
   Thus, we use the area to store the object size for small objects. */
static inline void lean_set_non_heap_header(lean_object * o, size_t sz, unsigned tag, unsigned other) {
    assert(sz > 0);
    assert(sz < (1ull << 16));
    assert(sz == 1 || !lean_is_big_object_tag(tag));
    o->m_rc       = 0;
    o->m_tag      = tag;
    o->m_other    = other;
    o->m_cs_sz    = sz;
}

/* `lean_set_non_heap_header` for (potentially) big objects such as arrays and strings. */
static inline void lean_set_non_heap_header_for_big(lean_object * o, unsigned tag, unsigned other) {
    lean_set_non_heap_header(o, 1, tag, other);
}

/* Constructor objects */

static inline unsigned lean_ctor_num_objs(lean_object * o) {
    assert(lean_is_ctor(o));
    return lean_ptr_other(o);
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
    assert(tag <= LeanMaxCtorTag && num_objs < LEAN_MAX_CTOR_FIELDS && scalar_sz < LEAN_MAX_CTOR_SCALARS_SIZE);
    lean_object * o = lean_alloc_ctor_memory(sizeof(lean_ctor_object) + sizeof(void*)*num_objs + scalar_sz);
    lean_set_st_header(o, tag, num_objs);
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
    o->m_tag = new_tag;
}

static inline void lean_ctor_release(b_lean_obj_arg o, unsigned i) {
    assert(i < lean_ctor_num_objs(o));
    lean_object ** objs = lean_ctor_obj_cptr(o);
    lean_dec(objs[i]);
    objs[i] = lean_box(0);
}

static inline size_t lean_ctor_get_usize(b_lean_obj_arg o, unsigned i) {
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

static inline double lean_ctor_get_float(b_lean_obj_arg o, unsigned offset) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    return *((double*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));
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

static inline void lean_ctor_set_float(b_lean_obj_arg o, unsigned offset, double v) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    *((double*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;
}

/* Closures */

static inline void * lean_closure_fun(lean_object * o) { return lean_to_closure(o)->m_fun; }
static inline unsigned lean_closure_arity(lean_object * o) { return lean_to_closure(o)->m_arity; }
static inline unsigned lean_closure_num_fixed(lean_object * o) { return lean_to_closure(o)->m_num_fixed; }
static inline lean_object ** lean_closure_arg_cptr(lean_object * o) { return lean_to_closure(o)->m_objs; }
static inline lean_obj_res lean_alloc_closure(void * fun, unsigned arity, unsigned num_fixed) {
    assert(arity > 0);
    assert(num_fixed < arity);
    lean_closure_object * o = (lean_closure_object*)lean_alloc_small_object(sizeof(lean_closure_object) + sizeof(void*)*num_fixed);
    lean_set_st_header((lean_object*)o, LeanClosure, 0);
    o->m_fun = fun;
    o->m_arity = arity;
    o->m_num_fixed = num_fixed;
    return (lean_object*)o;
}
static inline b_lean_obj_res lean_closure_get(b_lean_obj_arg o, unsigned i) {
    assert(i < lean_closure_num_fixed(o));
    return lean_to_closure(o)->m_objs[i];
}
static inline void lean_closure_set(u_lean_obj_arg o, unsigned i, lean_obj_arg a) {
    assert(i < lean_closure_num_fixed(o));
    lean_to_closure(o)->m_objs[i] = a;
}

LEAN_EXPORT lean_object* lean_apply_1(lean_object* f, lean_object* a1);
LEAN_EXPORT lean_object* lean_apply_2(lean_object* f, lean_object* a1, lean_object* a2);
LEAN_EXPORT lean_object* lean_apply_3(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3);
LEAN_EXPORT lean_object* lean_apply_4(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4);
LEAN_EXPORT lean_object* lean_apply_5(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5);
LEAN_EXPORT lean_object* lean_apply_6(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6);
LEAN_EXPORT lean_object* lean_apply_7(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7);
LEAN_EXPORT lean_object* lean_apply_8(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8);
LEAN_EXPORT lean_object* lean_apply_9(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9);
LEAN_EXPORT lean_object* lean_apply_10(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10);
LEAN_EXPORT lean_object* lean_apply_11(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10, lean_object* a11);
LEAN_EXPORT lean_object* lean_apply_12(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10, lean_object* a11, lean_object* a12);
LEAN_EXPORT lean_object* lean_apply_13(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10, lean_object* a11, lean_object* a12, lean_object* a13);
LEAN_EXPORT lean_object* lean_apply_14(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10, lean_object* a11, lean_object* a12, lean_object* a13, lean_object* a14);
LEAN_EXPORT lean_object* lean_apply_15(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10, lean_object* a11, lean_object* a12, lean_object* a13, lean_object* a14, lean_object* a15);
LEAN_EXPORT lean_object* lean_apply_16(lean_object* f, lean_object* a1, lean_object* a2, lean_object* a3, lean_object* a4, lean_object* a5, lean_object* a6, lean_object* a7, lean_object* a8, lean_object* a9, lean_object* a10, lean_object* a11, lean_object* a12, lean_object* a13, lean_object* a14, lean_object* a15, lean_object* a16);
LEAN_EXPORT lean_object* lean_apply_n(lean_object* f, unsigned n, lean_object** args);
/* Pre: n > 16 */
LEAN_EXPORT lean_object* lean_apply_m(lean_object* f, unsigned n, lean_object** args);

/* Arrays of objects (low level API) */
static inline lean_obj_res lean_alloc_array(size_t size, size_t capacity) {
    lean_array_object * o = (lean_array_object*)lean_alloc_object(sizeof(lean_array_object) + sizeof(void*)*capacity);
    lean_set_st_header((lean_object*)o, LeanArray, 0);
    o->m_size = size;
    o->m_capacity = capacity;
    return (lean_object*)o;
}
static inline size_t lean_array_size(b_lean_obj_arg o) { return lean_to_array(o)->m_size; }
static inline size_t lean_array_capacity(b_lean_obj_arg o) { return lean_to_array(o)->m_capacity; }
static inline size_t lean_array_byte_size(lean_object * o) {
    return sizeof(lean_array_object) + sizeof(void*)*lean_array_capacity(o);
}
static inline lean_object ** lean_array_cptr(lean_object * o) { return lean_to_array(o)->m_data; }
static inline void lean_array_set_size(u_lean_obj_arg o, size_t sz) {
    assert(lean_is_array(o));
    assert(lean_is_exclusive(o));
    assert(sz <= lean_array_capacity(o));
    lean_to_array(o)->m_size = sz;
}
static inline b_lean_obj_res lean_array_get_core(b_lean_obj_arg o, size_t i) {
    assert(i < lean_array_size(o));
    return lean_to_array(o)->m_data[i];
}
static inline void lean_array_set_core(u_lean_obj_arg o, size_t i, lean_obj_arg v) {
    /* Remark: we use this procedure to update non shared arrays in the heap,
       and when copying objects to compact region at compact.cpp */
    assert(!lean_has_rc(o) || lean_is_exclusive(o));
    assert(i < lean_array_size(o));
    lean_to_array(o)->m_data[i] = v;
}
LEAN_EXPORT lean_object * lean_array_mk(lean_obj_arg l);
LEAN_EXPORT lean_object * lean_array_to_list(lean_obj_arg a);

/* Arrays of objects (high level API) */

static inline lean_object * lean_array_sz(lean_obj_arg a) {
    lean_object * r = lean_box(lean_array_size(a));
    lean_dec(a);
    return r;
}

static inline lean_object * lean_array_get_size(b_lean_obj_arg a) {
    return lean_box(lean_array_size(a));
}

static inline lean_object * lean_mk_empty_array() {
    return lean_alloc_array(0, 0);
}

static inline lean_object * lean_mk_empty_array_with_capacity(b_lean_obj_arg capacity) {
    if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
    return lean_alloc_array(0, lean_unbox(capacity));
}

static inline lean_object * lean_array_uget(b_lean_obj_arg a, size_t i) {
    lean_object * r = lean_array_get_core(a, i); lean_inc(r);
    return r;
}

static inline lean_obj_res lean_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
    return lean_array_uget(a, lean_unbox(i));
}

LEAN_EXPORT lean_obj_res lean_array_get_panic(lean_obj_arg def_val);

static inline lean_object * lean_array_get(lean_obj_arg def_val, b_lean_obj_arg a, b_lean_obj_arg i) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        if (idx < lean_array_size(a)) {
            lean_dec(def_val);
            return lean_array_uget(a, idx);
        }
    }
    /* Recall that if `i` is not a scalar, then it must be out of bounds because
       i > LEAN_MAX_SMALL_NAT == MAX_UNSIGNED >> 1
       but each array entry is 8 bytes in 64-bit machines and 4 in 32-bit ones.
       In both cases, we would be out-of-memory. */
    return lean_array_get_panic(def_val);
}

LEAN_EXPORT lean_obj_res lean_copy_expand_array(lean_obj_arg a, bool expand);

static inline lean_obj_res lean_copy_array(lean_obj_arg a) {
    return lean_copy_expand_array(a, false);
}

static inline lean_obj_res lean_ensure_exclusive_array(lean_obj_arg a) {
    if (lean_is_exclusive(a)) return a;
    return lean_copy_array(a);
}

static inline lean_object * lean_array_uset(lean_obj_arg a, size_t i, lean_obj_arg v) {
    lean_object * r   = lean_ensure_exclusive_array(a);
    lean_object ** it = lean_array_cptr(r) + i;
    lean_dec(*it);
    *it = v;
    return r;
}

static inline lean_object * lean_array_fset(lean_obj_arg a, b_lean_obj_arg i, lean_obj_arg v) {
    return lean_array_uset(a, lean_unbox(i), v);
}

LEAN_EXPORT lean_obj_res lean_array_set_panic(lean_obj_arg a, lean_obj_arg v);

static inline lean_object * lean_array_set(lean_obj_arg a, b_lean_obj_arg i, lean_obj_arg v) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        if (idx < lean_array_size(a))
            return lean_array_uset(a, idx, v);
    }
    return lean_array_set_panic(a, v);
}

static inline lean_object * lean_array_pop(lean_obj_arg a) {
    lean_object * r  = lean_ensure_exclusive_array(a);
    size_t sz = lean_to_array(r)->m_size;
    lean_object ** last;
    if (sz == 0) return r;
    sz--;
    last = lean_array_cptr(r) + sz;
    lean_to_array(r)->m_size = sz;
    lean_dec(*last);
    return r;
}

static inline lean_object * lean_array_uswap(lean_obj_arg a, size_t i, size_t j) {
    lean_object * r   = lean_ensure_exclusive_array(a);
    lean_object ** it = lean_array_cptr(r);
    lean_object * v1  = it[i];
    it[i]        = it[j];
    it[j]        = v1;
    return r;
}

static inline lean_object * lean_array_fswap(lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg j) {
    return lean_array_uswap(a, lean_unbox(i), lean_unbox(j));
}

static inline lean_object * lean_array_swap(lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg j) {
    if (!lean_is_scalar(i) || !lean_is_scalar(j)) return a;
    size_t ui = lean_unbox(i);
    size_t uj = lean_unbox(j);
    size_t sz = lean_to_array(a)->m_size;
    if (ui >= sz || uj >= sz) return a;
    return lean_array_uswap(a, ui, uj);
}

LEAN_EXPORT lean_object * lean_array_push(lean_obj_arg a, lean_obj_arg v);
LEAN_EXPORT lean_object * lean_mk_array(lean_obj_arg n, lean_obj_arg v);

/* Array of scalars */

static inline lean_obj_res lean_alloc_sarray(unsigned elem_size, size_t size, size_t capacity) {
    lean_sarray_object * o = (lean_sarray_object*)lean_alloc_object(sizeof(lean_sarray_object) + elem_size*capacity);
    lean_set_st_header((lean_object*)o, LeanScalarArray, elem_size);
    o->m_size = size;
    o->m_capacity = capacity;
    return (lean_object*)o;
}
static inline unsigned lean_sarray_elem_size(lean_object * o) {
    assert(lean_is_sarray(o));
    return lean_ptr_other(o);
}
static inline size_t lean_sarray_capacity(lean_object * o) { return lean_to_sarray(o)->m_capacity; }
static inline size_t lean_sarray_byte_size(lean_object * o) {
    return sizeof(lean_sarray_object) + lean_sarray_elem_size(o)*lean_sarray_capacity(o);
}
static inline size_t lean_sarray_size(b_lean_obj_arg o) { return lean_to_sarray(o)->m_size; }
static inline void lean_sarray_set_size(u_lean_obj_arg o, size_t sz) {
    assert(lean_is_exclusive(o));
    assert(sz <= lean_sarray_capacity(o));
    lean_to_sarray(o)->m_size = sz;
}
static inline uint8_t* lean_sarray_cptr(lean_object * o) { return lean_to_sarray(o)->m_data; }

/* Remark: expand sarray API after we add better support in the compiler */

/* ByteArray (special case of Array of Scalars) */

LEAN_EXPORT lean_obj_res lean_byte_array_mk(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_byte_array_data(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_byte_array(lean_obj_arg a);
LEAN_EXPORT uint64_t lean_byte_array_hash(b_lean_obj_arg a);

static inline lean_obj_res lean_mk_empty_byte_array(b_lean_obj_arg capacity) {
    if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
    return lean_alloc_sarray(1, 0, lean_unbox(capacity));
}

static inline lean_obj_res lean_byte_array_size(b_lean_obj_arg a) {
    return lean_box(lean_sarray_size(a));
}
static inline uint8_t lean_byte_array_uget(b_lean_obj_arg a, size_t i) {
    assert(i < lean_sarray_size(a));
    return lean_sarray_cptr(a)[i];
}
static inline uint8_t lean_byte_array_get(b_lean_obj_arg a, b_lean_obj_arg i) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        return idx < lean_sarray_size(a) ? lean_byte_array_uget(a, idx) : 0;
    } else {
        /* The index must be out of bounds. Otherwise we would be out of memory. */
        return 0;
    }
}
static inline uint8_t lean_byte_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
    return lean_byte_array_uget(a, lean_unbox(i));
}

LEAN_EXPORT lean_obj_res lean_byte_array_push(lean_obj_arg a, uint8_t b);

static inline lean_object * lean_byte_array_uset(lean_obj_arg a, size_t i, uint8_t v) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_byte_array(a);
    uint8_t * it = lean_sarray_cptr(r) + i;
    *it = v;
    return r;
}

static inline lean_obj_res lean_byte_array_set(lean_obj_arg a, b_lean_obj_arg i, uint8_t b) {
    if (!lean_is_scalar(i)) {
        return a;
    } else {
        size_t idx = lean_unbox(i);
        if (idx >= lean_sarray_size(a)) {
            return a;
        } else {
            return lean_byte_array_uset(a, idx, b);
        }
    }
}

static inline lean_obj_res lean_byte_array_fset(lean_obj_arg a, b_lean_obj_arg i, uint8_t b) {
    return lean_byte_array_uset(a, lean_unbox(i), b);
}

/* FloatArray (special case of Array of Scalars) */

LEAN_EXPORT lean_obj_res lean_float_array_mk(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_float_array_data(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_float_array(lean_obj_arg a);

static inline lean_obj_res lean_mk_empty_float_array(b_lean_obj_arg capacity) {
    if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
    return lean_alloc_sarray(sizeof(double), 0, lean_unbox(capacity)); // NOLINT
}

static inline lean_obj_res lean_float_array_size(b_lean_obj_arg a) {
    return lean_box(lean_sarray_size(a));
}

static inline double * lean_float_array_cptr(b_lean_obj_arg a) {
    return (double*)(lean_sarray_cptr(a)); // NOLINT
}

static inline double lean_float_array_uget(b_lean_obj_arg a, size_t i) {
    return lean_float_array_cptr(a)[i];
}

static inline double lean_float_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
    return lean_float_array_uget(a, lean_unbox(i));
}

static inline double lean_float_array_get(b_lean_obj_arg a, b_lean_obj_arg i) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        return idx < lean_sarray_size(a) ? lean_float_array_uget(a, idx) : 0.0;
    } else {
        /* The index must be out of bounds. Otherwise we would be out of memory. */
        return 0.0;
    }
}

LEAN_EXPORT lean_obj_res lean_float_array_push(lean_obj_arg a, double d);

static inline lean_obj_res lean_float_array_uset(lean_obj_arg a, size_t i, double d) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_float_array(a);
    double * it = lean_float_array_cptr(r) + i;
    *it = d;
    return r;
}

static inline lean_obj_res lean_float_array_fset(lean_obj_arg a, b_lean_obj_arg i, double d) {
    return lean_float_array_uset(a, lean_unbox(i), d);
}

static inline lean_obj_res lean_float_array_set(lean_obj_arg a, b_lean_obj_arg i, double d) {
    if (!lean_is_scalar(i)) {
        return a;
    } else {
        size_t idx = lean_unbox(i);
        if (idx >= lean_sarray_size(a)) {
            return a;
        } else {
            return lean_float_array_uset(a, idx, d);
        }
    }
}

/* Strings */

static inline lean_obj_res lean_alloc_string(size_t size, size_t capacity, size_t len) {
    lean_string_object * o = (lean_string_object*)lean_alloc_object(sizeof(lean_string_object) + capacity);
    lean_set_st_header((lean_object*)o, LeanString, 0);
    o->m_size = size;
    o->m_capacity = capacity;
    o->m_length = len;
    return (lean_object*)o;
}
LEAN_EXPORT size_t lean_utf8_strlen(char const * str);
LEAN_EXPORT size_t lean_utf8_n_strlen(char const * str, size_t n);
static inline size_t lean_string_capacity(lean_object * o) { return lean_to_string(o)->m_capacity; }
static inline size_t lean_string_byte_size(lean_object * o) { return sizeof(lean_string_object) + lean_string_capacity(o); }
/* instance : inhabited char := ⟨'A'⟩ */
static inline uint32_t lean_char_default_value() { return 'A'; }
LEAN_EXPORT lean_obj_res lean_mk_string_unchecked(char const * s, size_t sz, size_t len);
LEAN_EXPORT lean_obj_res lean_mk_string_from_bytes(char const * s, size_t sz);
LEAN_EXPORT lean_obj_res lean_mk_string_from_bytes_unchecked(char const * s, size_t sz);
LEAN_EXPORT lean_obj_res lean_mk_ascii_string_unchecked(char const * s);
LEAN_EXPORT lean_obj_res lean_mk_string(char const * s);
static inline char const * lean_string_cstr(b_lean_obj_arg o) {
    assert(lean_is_string(o));
    return lean_to_string(o)->m_data;
}
static inline size_t lean_string_size(b_lean_obj_arg o) { return lean_to_string(o)->m_size; }
static inline size_t lean_string_len(b_lean_obj_arg o) { return lean_to_string(o)->m_length; }
LEAN_EXPORT lean_obj_res lean_string_push(lean_obj_arg s, uint32_t c);
LEAN_EXPORT lean_obj_res lean_string_append(lean_obj_arg s1, b_lean_obj_arg s2);
static inline lean_obj_res lean_string_length(b_lean_obj_arg s) { return lean_box(lean_string_len(s)); }
LEAN_EXPORT lean_obj_res lean_string_mk(lean_obj_arg cs);
LEAN_EXPORT lean_obj_res lean_string_data(lean_obj_arg s);
LEAN_EXPORT uint32_t  lean_string_utf8_get(b_lean_obj_arg s, b_lean_obj_arg i);
LEAN_EXPORT uint32_t lean_string_utf8_get_fast_cold(char const * str, size_t i, size_t size, unsigned char c);
static inline uint32_t lean_string_utf8_get_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
  char const * str = lean_string_cstr(s);
  size_t idx = lean_unbox(i);
  unsigned char c = (unsigned char)(str[idx]);
  if ((c & 0x80) == 0) return c;
  return lean_string_utf8_get_fast_cold(str, idx, lean_string_size(s), c);
}
static inline uint8_t lean_string_get_byte_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
  char const * str = lean_string_cstr(s);
  size_t idx = lean_unbox(i);
  return str[idx];
}

LEAN_EXPORT lean_obj_res lean_string_utf8_next(b_lean_obj_arg s, b_lean_obj_arg i);
LEAN_EXPORT lean_obj_res lean_string_utf8_next_fast_cold(size_t i, unsigned char c);
static inline lean_obj_res lean_string_utf8_next_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
  char const * str = lean_string_cstr(s);
  size_t idx = lean_unbox(i);
  unsigned char c = (unsigned char)(str[idx]);
  if ((c & 0x80) == 0) return lean_box(idx+1);
  return lean_string_utf8_next_fast_cold(idx, c);
}

LEAN_EXPORT lean_obj_res lean_string_utf8_prev(b_lean_obj_arg s, b_lean_obj_arg i);
LEAN_EXPORT lean_obj_res lean_string_utf8_set(lean_obj_arg s, b_lean_obj_arg i, uint32_t c);
static inline uint8_t lean_string_utf8_at_end(b_lean_obj_arg s, b_lean_obj_arg i) {
    return !lean_is_scalar(i) || lean_unbox(i) >= lean_string_size(s) - 1;
}
LEAN_EXPORT lean_obj_res lean_string_utf8_extract(b_lean_obj_arg s, b_lean_obj_arg b, b_lean_obj_arg e);
static inline lean_obj_res lean_string_utf8_byte_size(b_lean_obj_arg s) { return lean_box(lean_string_size(s) - 1); }
LEAN_EXPORT bool lean_string_eq_cold(b_lean_obj_arg s1, b_lean_obj_arg s2);
static inline bool lean_string_eq(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    return s1 == s2 || (lean_string_size(s1) == lean_string_size(s2) && lean_string_eq_cold(s1, s2));
}
static inline bool lean_string_ne(b_lean_obj_arg s1, b_lean_obj_arg s2) { return !lean_string_eq(s1, s2); }
LEAN_EXPORT bool lean_string_lt(b_lean_obj_arg s1, b_lean_obj_arg s2);
static inline uint8_t lean_string_dec_eq(b_lean_obj_arg s1, b_lean_obj_arg s2) { return lean_string_eq(s1, s2); }
static inline uint8_t lean_string_dec_lt(b_lean_obj_arg s1, b_lean_obj_arg s2) { return lean_string_lt(s1, s2); }
LEAN_EXPORT uint64_t lean_string_hash(b_lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_string_of_usize(size_t);

/* Thunks */

static inline lean_obj_res lean_mk_thunk(lean_obj_arg c) {
    lean_thunk_object * o = (lean_thunk_object*)lean_alloc_small_object(sizeof(lean_thunk_object));
    lean_set_st_header((lean_object*)o, LeanThunk, 0);
    o->m_value   = (lean_object*)0;
    o->m_closure = c;
    return (lean_object*)o;
}

/* Thunk.pure : A -> Thunk A */
static inline lean_obj_res lean_thunk_pure(lean_obj_arg v) {
    lean_thunk_object * o = (lean_thunk_object*)lean_alloc_small_object(sizeof(lean_thunk_object));
    lean_set_st_header((lean_object*)o, LeanThunk, 0);
    o->m_value   = v;
    o->m_closure = (lean_object*)0;
    return (lean_object*)o;
}

LEAN_EXPORT lean_object * lean_thunk_get_core(lean_object * t);

static inline b_lean_obj_res lean_thunk_get(b_lean_obj_arg t) {
    lean_object * r = lean_to_thunk(t)->m_value;
    if (r) return r;
    return lean_thunk_get_core(t);
}

/* Primitive for implementing Thunk.get : Thunk A -> A */
static inline lean_obj_res lean_thunk_get_own(b_lean_obj_arg t) {
    lean_object * r = lean_thunk_get(t);
    lean_inc(r);
    return r;
}

/* Tasks */

LEAN_EXPORT void lean_init_task_manager(void);
LEAN_EXPORT void lean_init_task_manager_using(unsigned num_workers);
LEAN_EXPORT void lean_finalize_task_manager(void);

LEAN_EXPORT lean_obj_res lean_task_spawn_core(lean_obj_arg c, unsigned prio, bool keep_alive);
/* Run a closure `Unit -> A` as a `Task A` */
static inline lean_obj_res lean_task_spawn(lean_obj_arg c, lean_obj_arg prio) { return lean_task_spawn_core(c, lean_unbox(prio), false); }
/* Convert a value `a : A` into `Task A` */
LEAN_EXPORT lean_obj_res lean_task_pure(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_task_bind_core(lean_obj_arg x, lean_obj_arg f, unsigned prio, bool sync, bool keep_alive);
/* Task.bind (x : Task A) (f : A -> Task B) (prio : Nat) (sync : Bool) : Task B */
static inline lean_obj_res lean_task_bind(lean_obj_arg x, lean_obj_arg f, lean_obj_arg prio, uint8_t sync) { return lean_task_bind_core(x, f, lean_unbox(prio), sync, false); }
LEAN_EXPORT lean_obj_res lean_task_map_core(lean_obj_arg f, lean_obj_arg t, unsigned prio, bool sync, bool keep_alive);
/* Task.map (f : A -> B) (t : Task A) (prio : Nat) (sync : Bool) : Task B */
static inline lean_obj_res lean_task_map(lean_obj_arg f, lean_obj_arg t, lean_obj_arg prio, uint8_t sync) { return lean_task_map_core(f, t, lean_unbox(prio), sync, false); }
LEAN_EXPORT b_lean_obj_res lean_task_get(b_lean_obj_arg t);
/* Primitive for implementing Task.get : Task A -> A */
static inline lean_obj_res lean_task_get_own(lean_obj_arg t) {
    lean_object * r = lean_task_get(t);
    lean_inc(r);
    lean_dec(t);
    return r;
}

/* primitive for implementing `IO.checkCanceled : IO Bool` */
LEAN_EXPORT bool lean_io_check_canceled_core(void);
/* primitive for implementing `IO.cancel : Task a -> IO Unit` */
LEAN_EXPORT void lean_io_cancel_core(b_lean_obj_arg t);
/* primitive for implementing `IO.getTaskState : Task a -> IO TaskState` */
LEAN_EXPORT uint8_t lean_io_get_task_state_core(b_lean_obj_arg t);
/* primitive for implementing `IO.waitAny : List (Task a) -> IO (Task a)` */
LEAN_EXPORT b_lean_obj_res lean_io_wait_any_core(b_lean_obj_arg task_list);

/* External objects */

static inline lean_object * lean_alloc_external(lean_external_class * cls, void * data) {
    lean_external_object * o = (lean_external_object*)lean_alloc_small_object(sizeof(lean_external_object));
    lean_set_st_header((lean_object*)o, LeanExternal, 0);
    o->m_class   = cls;
    o->m_data    = data;
    return (lean_object*)o;
}

static inline lean_external_class * lean_get_external_class(lean_object * o) {
    return lean_to_external(o)->m_class;
}

static inline void * lean_get_external_data(lean_object * o) {
    return lean_to_external(o)->m_data;
}

static inline lean_object * lean_set_external_data(lean_object * o, void * data) {
    if (lean_is_exclusive(o)) {
        lean_to_external(o)->m_data = data;
        return o;
    } else {
        lean_object * o_new = lean_alloc_external(lean_get_external_class(o), data);
        lean_dec_ref(o);
        return o_new;
    }
}

/* Natural numbers */

#define LEAN_MAX_SMALL_NAT (SIZE_MAX >> 1)

LEAN_EXPORT lean_object * lean_nat_big_succ(lean_object * a);
LEAN_EXPORT lean_object * lean_nat_big_add(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_big_sub(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_big_mul(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_overflow_mul(size_t a1, size_t a2);
LEAN_EXPORT lean_object * lean_nat_big_div(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_big_mod(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_nat_big_eq(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_nat_big_le(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_nat_big_lt(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_big_land(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_big_lor(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_nat_big_xor(lean_object * a1, lean_object * a2);

LEAN_EXPORT lean_obj_res lean_cstr_to_nat(char const * n);
LEAN_EXPORT lean_obj_res lean_big_usize_to_nat(size_t n);
LEAN_EXPORT lean_obj_res lean_big_uint64_to_nat(uint64_t n);
static inline lean_obj_res lean_usize_to_nat(size_t n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
        return lean_box(n);
    else
        return lean_big_usize_to_nat(n);
}
static inline lean_obj_res lean_unsigned_to_nat(unsigned n) {
    return lean_usize_to_nat(n);
}
static inline lean_obj_res lean_uint64_to_nat(uint64_t n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
        return lean_box(n);
    else
        return lean_big_uint64_to_nat(n);
}

static inline lean_obj_res lean_nat_succ(b_lean_obj_arg a) {
    if (LEAN_LIKELY(lean_is_scalar(a)))
        return lean_usize_to_nat(lean_unbox(a) + 1);
    else
        return lean_nat_big_succ(a);
}

static inline lean_obj_res lean_nat_add(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2)))
        return lean_usize_to_nat(lean_unbox(a1) + lean_unbox(a2));
    else
        return lean_nat_big_add(a1, a2);
}

static inline lean_obj_res lean_nat_sub(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        size_t n2 = lean_unbox(a2);
        if (n1 < n2)
            return lean_box(0);
        else
            return lean_box(n1 - n2);
    } else {
        return lean_nat_big_sub(a1, a2);
    }
}

static inline lean_obj_res lean_nat_mul(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        if (n1 == 0)
            return a1;
        size_t n2 = lean_unbox(a2);
        size_t r  = n1*n2;
        if (r <= LEAN_MAX_SMALL_NAT && r / n1 == n2)
            return lean_box(r);
        else
            return lean_nat_overflow_mul(n1, n2);
    } else {
        return lean_nat_big_mul(a1, a2);
    }
}

static inline lean_obj_res lean_nat_div(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        size_t n2 = lean_unbox(a2);
        if (n2 == 0)
            return lean_box(0);
        else
            return lean_box(n1 / n2);
    } else {
        return lean_nat_big_div(a1, a2);
    }
}

static inline lean_obj_res lean_nat_mod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        size_t n1 = lean_unbox(a1);
        size_t n2 = lean_unbox(a2);
        if (n2 == 0)
            return lean_box(n1);
        else
            return lean_box(n1 % n2);
    } else {
        return lean_nat_big_mod(a1, a2);
    }
}

static inline bool lean_nat_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return a1 == a2;
    } else {
        return lean_nat_big_eq(a1, a2);
    }
}

static inline uint8_t lean_nat_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return lean_nat_eq(a1, a2);
}

static inline bool lean_nat_ne(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return !lean_nat_eq(a1, a2);
}

static inline bool lean_nat_le(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return a1 <= a2;
    } else {
        return lean_nat_big_le(a1, a2);
    }
}

static inline uint8_t lean_nat_dec_le(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return lean_nat_le(a1, a2);
}

static inline bool lean_nat_lt(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return a1 < a2;
    } else {
        return lean_nat_big_lt(a1, a2);
    }
}

static inline uint8_t lean_nat_dec_lt(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return lean_nat_lt(a1, a2);
}

static inline lean_obj_res lean_nat_land(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return (lean_object*)((size_t)(a1) & (size_t)(a2));
    } else {
        return lean_nat_big_land(a1, a2);
    }
}

static inline lean_obj_res lean_nat_lor(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return (lean_object*)((size_t)(a1) | (size_t)(a2));
    } else {
        return lean_nat_big_lor(a1, a2);
    }
}

static inline lean_obj_res lean_nat_lxor(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_box(lean_unbox(a1) ^ lean_unbox(a2));
    } else {
        return lean_nat_big_xor(a1, a2);
    }
}

LEAN_EXPORT lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2);
LEAN_EXPORT lean_obj_res lean_nat_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2);
LEAN_EXPORT lean_obj_res lean_nat_pow(b_lean_obj_arg a1, b_lean_obj_arg a2);
LEAN_EXPORT lean_obj_res lean_nat_gcd(b_lean_obj_arg a1, b_lean_obj_arg a2);
LEAN_EXPORT lean_obj_res lean_nat_log2(b_lean_obj_arg a);

/* Integers */

#define LEAN_MAX_SMALL_INT (sizeof(void*) == 8 ? INT_MAX : (INT_MAX >> 1))
#define LEAN_MIN_SMALL_INT (sizeof(void*) == 8 ? INT_MIN : (INT_MIN >> 1))
LEAN_EXPORT lean_object * lean_int_big_neg(lean_object * a);
LEAN_EXPORT lean_object * lean_int_big_add(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_int_big_sub(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_int_big_mul(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_int_big_div(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_int_big_mod(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_int_big_ediv(lean_object * a1, lean_object * a2);
LEAN_EXPORT lean_object * lean_int_big_emod(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_int_big_eq(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_int_big_le(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_int_big_lt(lean_object * a1, lean_object * a2);
LEAN_EXPORT bool lean_int_big_nonneg(lean_object * a);

LEAN_EXPORT lean_object * lean_cstr_to_int(char const * n);
LEAN_EXPORT lean_object * lean_big_int_to_int(int n);
LEAN_EXPORT lean_object * lean_big_size_t_to_int(size_t n);
LEAN_EXPORT lean_object * lean_big_int64_to_int(int64_t n);

static inline lean_obj_res lean_int_to_int(int n) {
    if (sizeof(void*) == 8)
        return lean_box((unsigned)(n));
    else if (LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT)
        return lean_box((unsigned)(n));
    else
        return lean_big_int_to_int(n);
}

static inline lean_obj_res lean_int64_to_int(int64_t n) {
    if (LEAN_LIKELY(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT))
        return lean_box((unsigned)((int)n)); /* NOLINT */
    else
        return lean_big_int64_to_int(n);
}

static inline int64_t lean_scalar_to_int64(b_lean_obj_arg a) {
    assert(lean_is_scalar(a));
    if (sizeof(void*) == 8)
        return (int)((unsigned)lean_unbox(a)); /* NOLINT */
    else
        return ((int)((size_t)a)) >> 1; /* NOLINT */
}

static inline int lean_scalar_to_int(b_lean_obj_arg a) {
    assert(lean_is_scalar(a));
    if (sizeof(void*) == 8)
        return (int)((unsigned)lean_unbox(a)); /* NOLINT */
    else
        return ((int)((size_t)a)) >> 1; /* NOLINT */
}

static inline lean_obj_res lean_nat_to_int(lean_obj_arg a) {
    if (lean_is_scalar(a)) {
        size_t v = lean_unbox(a);
        if (v <= LEAN_MAX_SMALL_INT)
            return a;
        else
            return lean_big_size_t_to_int(v);
    } else {
        return a;
    }
}

static inline lean_obj_res lean_int_neg(b_lean_obj_arg a) {
    if (LEAN_LIKELY(lean_is_scalar(a))) {
        return lean_int64_to_int(-lean_scalar_to_int64(a));
    } else {
        return lean_int_big_neg(a);
    }
}

static inline lean_obj_res lean_int_neg_succ_of_nat(lean_obj_arg a) {
    lean_obj_res s  = lean_nat_succ(a);    lean_dec(a);
    lean_obj_res i  = lean_nat_to_int(s);  /* Recall that `lean_nat_to_int` consumes the argument */
    lean_obj_res r  = lean_int_neg(i);     lean_dec(i);
    return r;
}

static inline lean_obj_res lean_int_add(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_int64_to_int(lean_scalar_to_int64(a1) + lean_scalar_to_int64(a2));
    } else {
        return lean_int_big_add(a1, a2);
    }
}

static inline lean_obj_res lean_int_sub(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_int64_to_int(lean_scalar_to_int64(a1) - lean_scalar_to_int64(a2));
    } else {
        return lean_int_big_sub(a1, a2);
    }
}

static inline lean_obj_res lean_int_mul(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_int64_to_int(lean_scalar_to_int64(a1) * lean_scalar_to_int64(a2));
    } else {
        return lean_int_big_mul(a1, a2);
    }
}

static inline lean_obj_res lean_int_div(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        if (sizeof(void*) == 8) {
            /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
            int64_t v1 = lean_scalar_to_int(a1);
            int64_t v2 = lean_scalar_to_int(a2);
            if (v2 == 0)
                return lean_box(0);
            else
                return lean_int64_to_int(v1 / v2);
        } else {
            /* 32-bit version */
            int v1 = lean_scalar_to_int(a1);
            int v2 = lean_scalar_to_int(a2);
            if (v2 == 0)
                return lean_box(0);
            else
                return lean_int_to_int(v1 / v2);
        }
    } else {
        return lean_int_big_div(a1, a2);
    }
}

static inline lean_obj_res lean_int_mod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        if (sizeof(void*) == 8) {
            /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
            int64_t v1 = lean_scalar_to_int64(a1);
            int64_t v2 = lean_scalar_to_int64(a2);
            if (v2 == 0)
                return a1;
            else
                return lean_int64_to_int(v1 % v2);
        } else {
            /* 32-bit version */
            int v1 = lean_scalar_to_int(a1);
            int v2 = lean_scalar_to_int(a2);
            if (v2 == 0)
                return a1;
            else
                return lean_int_to_int(v1 % v2);
        }
    } else {
        return lean_int_big_mod(a1, a2);
    }
}

/*
lean_int_ediv and lean_int_emod implement "Euclidean" division and modulus using the
algorithm in:
  Division and Modulus for Computer Scientists
  Daan Leijen
  https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

*/

static inline lean_obj_res lean_int_ediv(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        if (sizeof(void*) == 8) {
            /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
            int64_t n = lean_scalar_to_int(a1);
            int64_t d = lean_scalar_to_int(a2);
            if (d == 0)
                return lean_box(0);
            else {
                int64_t q = n / d;
                int64_t r = n % d;
                if (r < 0)
                    q = (d > 0) ? q - 1 : q + 1;
                return lean_int64_to_int(q);
            }
        } else {
            /* 32-bit version */
            int n = lean_scalar_to_int(a1);
            int d = lean_scalar_to_int(a2);
            if (d == 0) {
                return lean_box(0);
            } else {
                int q = n / d;
                int r = n % d;
                if (r < 0)
                    q = (d > 0) ? q - 1 : q + 1;
                return lean_int_to_int(q);
            }
        }
    } else {
        return lean_int_big_ediv(a1, a2);
    }
}

static inline lean_obj_res lean_int_emod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        if (sizeof(void*) == 8) {
            /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
            int64_t n = lean_scalar_to_int64(a1);
            int64_t d = lean_scalar_to_int64(a2);
            if (d == 0) {
                return a1;
            } else {
                int64_t r = n % d;
                if (r < 0)
                    r = (d > 0) ? r + d : r - d;
                return lean_int64_to_int(r);
            }
        } else {
            /* 32-bit version */
            int n = lean_scalar_to_int(a1);
            int d = lean_scalar_to_int(a2);
            if (d == 0)
                return a1;
            else {
                int r = n % d;
                if (r < 0)
                    r = (d > 0) ? r + d : r - d;
                return lean_int_to_int(r);
            }
        }
    } else {
        return lean_int_big_emod(a1, a2);
    }
}

static inline bool lean_int_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return a1 == a2;
    } else {
        return lean_int_big_eq(a1, a2);
    }
}

static inline bool lean_int_ne(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    return !lean_int_eq(a1, a2);
}

static inline bool lean_int_le(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_scalar_to_int(a1) <= lean_scalar_to_int(a2);
    } else {
        return lean_int_big_le(a1, a2);
    }
}

static inline bool lean_int_lt(b_lean_obj_arg a1, b_lean_obj_arg a2) {
    if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
        return lean_scalar_to_int(a1) < lean_scalar_to_int(a2);
    } else {
        return lean_int_big_lt(a1, a2);
    }
}

LEAN_EXPORT lean_obj_res lean_big_int_to_nat(lean_obj_arg a);
static inline lean_obj_res lean_int_to_nat(lean_obj_arg a) {
    assert(!lean_int_lt(a, lean_box(0)));
    if (lean_is_scalar(a)) {
        return a;
    } else {
        return lean_big_int_to_nat(a);
    }
}

static inline lean_obj_res lean_nat_abs(b_lean_obj_arg i) {
    if (lean_int_lt(i, lean_box(0))) {
        return lean_int_to_nat(lean_int_neg(i));
    } else {
        lean_inc(i);
        return lean_int_to_nat(i);
    }
}

static inline uint8_t lean_int_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_int_eq(a1, a2); }

static inline uint8_t lean_int_dec_le(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_int_le(a1, a2); }

static inline uint8_t lean_int_dec_lt(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_int_lt(a1, a2); }

static inline uint8_t lean_int_dec_nonneg(b_lean_obj_arg a) {
    if (LEAN_LIKELY(lean_is_scalar(a)))
        return lean_scalar_to_int(a) >= 0;
    else
        return lean_int_big_nonneg(a);
}

/* Bool */

static inline uint8_t lean_bool_to_uint8(uint8_t a) { return a; }
static inline uint16_t lean_bool_to_uint16(uint8_t a) { return (uint16_t)a; }
static inline uint32_t lean_bool_to_uint32(uint8_t a) { return (uint32_t)a; }
static inline uint64_t lean_bool_to_uint64(uint8_t a) { return (uint64_t)a; }
static inline size_t lean_bool_to_usize(uint8_t a) { return (size_t)a; }
static inline uint8_t lean_bool_to_int8(uint8_t a) { return (uint8_t)(int8_t)a; }
static inline uint16_t lean_bool_to_int16(uint8_t a) { return (uint16_t)(int16_t)a; }
static inline uint32_t lean_bool_to_int32(uint8_t a) { return (uint32_t)(int32_t)a; }
static inline uint64_t lean_bool_to_int64(uint8_t a) { return (uint64_t)(int64_t)a; }
static inline size_t lean_bool_to_isize(uint8_t a) { return (size_t)(ptrdiff_t)a; }


/* UInt8 */

LEAN_EXPORT uint8_t lean_uint8_of_big_nat(b_lean_obj_arg a);
static inline uint8_t lean_uint8_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint8_t)(lean_unbox(a)) : lean_uint8_of_big_nat(a); }
/* Remark: the following function is used to implement the constructor `UInt8.mk`. We can't annotate constructors with `@&` */
static inline uint8_t lean_uint8_of_nat_mk(lean_obj_arg a) { uint8_t r = lean_uint8_of_nat(a); lean_dec(a); return r; }
static inline lean_obj_res lean_uint8_to_nat(uint8_t a) { return lean_usize_to_nat((size_t)a); }
static inline uint8_t lean_uint8_add(uint8_t a1, uint8_t a2) { return a1+a2; }
static inline uint8_t lean_uint8_sub(uint8_t a1, uint8_t a2) { return a1-a2; }
static inline uint8_t lean_uint8_mul(uint8_t a1, uint8_t a2) { return a1*a2; }
static inline uint8_t lean_uint8_div(uint8_t a1, uint8_t a2) { return a2 == 0 ? 0  : a1/a2; }
static inline uint8_t lean_uint8_mod(uint8_t a1, uint8_t a2) { return a2 == 0 ? a1 : a1%a2; }
static inline uint8_t lean_uint8_land(uint8_t a, uint8_t b) { return a & b; }
static inline uint8_t lean_uint8_lor(uint8_t a, uint8_t b) { return a | b; }
static inline uint8_t lean_uint8_xor(uint8_t a, uint8_t b) { return a ^ b; }
static inline uint8_t lean_uint8_shift_left(uint8_t a, uint8_t b) { return a << (b % 8); }
static inline uint8_t lean_uint8_shift_right(uint8_t a, uint8_t b) { return a >> (b % 8); }
static inline uint8_t lean_uint8_complement(uint8_t a) { return ~a; }
static inline uint8_t lean_uint8_log2(uint8_t a) {
    uint8_t res = 0;
    while (a >= 2) {
        res++;
        a /= 2;
    }
    return res;
}
static inline uint8_t lean_uint8_dec_eq(uint8_t a1, uint8_t a2) { return a1 == a2; }
static inline uint8_t lean_uint8_dec_lt(uint8_t a1, uint8_t a2) { return a1 < a2; }
static inline uint8_t lean_uint8_dec_le(uint8_t a1, uint8_t a2) { return a1 <= a2; }


/* UInt8 -> other */
static inline uint16_t lean_uint8_to_uint16(uint8_t a) { return ((uint16_t)a); }
static inline uint32_t lean_uint8_to_uint32(uint8_t a) { return ((uint32_t)a); }
static inline uint64_t lean_uint8_to_uint64(uint8_t a) { return ((uint64_t)a); }

/* UInt16 */

LEAN_EXPORT uint16_t lean_uint16_of_big_nat(b_lean_obj_arg a);
static inline uint16_t lean_uint16_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (int16_t)(lean_unbox(a)) : lean_uint16_of_big_nat(a); }
/* Remark: the following function is used to implement the constructor `UInt16.mk`. We can't annotate constructors with `@&` */
static inline uint16_t lean_uint16_of_nat_mk(lean_obj_arg a) { uint16_t r = lean_uint16_of_nat(a); lean_dec(a); return r; }
static inline lean_obj_res lean_uint16_to_nat(uint16_t a) { return lean_usize_to_nat((size_t)a); }
static inline uint16_t lean_uint16_add(uint16_t a1, uint16_t a2) { return a1+a2; }
static inline uint16_t lean_uint16_sub(uint16_t a1, uint16_t a2) { return a1-a2; }
static inline uint16_t lean_uint16_mul(uint16_t a1, uint16_t a2) { return a1*a2; }
static inline uint16_t lean_uint16_div(uint16_t a1, uint16_t a2) { return a2 == 0 ? 0  : a1/a2; }
static inline uint16_t lean_uint16_mod(uint16_t a1, uint16_t a2) { return a2 == 0 ? a1 : a1%a2; }
static inline uint16_t lean_uint16_land(uint16_t a, uint16_t b) { return a & b; }
static inline uint16_t lean_uint16_lor(uint16_t a, uint16_t b) { return a | b; }
static inline uint16_t lean_uint16_xor(uint16_t a, uint16_t b) { return a ^ b; }
static inline uint16_t lean_uint16_shift_left(uint16_t a, uint16_t b) { return a << (b % 16); }
static inline uint16_t lean_uint16_shift_right(uint16_t a, uint16_t b) { return a >> (b % 16); }
static inline uint16_t lean_uint16_complement(uint16_t a) { return ~a; }
static inline uint16_t lean_uint16_log2(uint16_t a) {
    uint16_t res = 0;
    while (a >= 2) {
        res++;
        a /= 2;
    }
    return res;
}
static inline uint8_t lean_uint16_dec_eq(uint16_t a1, uint16_t a2) { return a1 == a2; }
static inline uint8_t lean_uint16_dec_lt(uint16_t a1, uint16_t a2) { return a1 < a2; }
static inline uint8_t lean_uint16_dec_le(uint16_t a1, uint16_t a2) { return a1 <= a2; }

/* UInt16 -> other */
static inline uint8_t lean_uint16_to_uint8(uint16_t a) { return ((uint8_t)a); }
static inline uint32_t lean_uint16_to_uint32(uint16_t a) { return ((uint32_t)a); }
static inline uint64_t lean_uint16_to_uint64(uint16_t a) { return ((uint64_t)a); }

/* UInt32 */

LEAN_EXPORT uint32_t lean_uint32_of_big_nat(b_lean_obj_arg a);
static inline uint32_t lean_uint32_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint32_t)(lean_unbox(a)) : lean_uint32_of_big_nat(a); }
/* Remark: the following function is used to implement the constructor `UInt32.mk`. We can't annotate constructors with `@&` */
static inline uint32_t lean_uint32_of_nat_mk(lean_obj_arg a) { uint32_t r = lean_uint32_of_nat(a); lean_dec(a); return r; }
static inline lean_obj_res lean_uint32_to_nat(uint32_t a) { return lean_usize_to_nat((size_t)a); }
static inline uint32_t lean_uint32_add(uint32_t a1, uint32_t a2) { return a1+a2; }
static inline uint32_t lean_uint32_sub(uint32_t a1, uint32_t a2) { return a1-a2; }
static inline uint32_t lean_uint32_mul(uint32_t a1, uint32_t a2) { return a1*a2; }
static inline uint32_t lean_uint32_div(uint32_t a1, uint32_t a2) { return a2 == 0 ? 0  : a1/a2; }
static inline uint32_t lean_uint32_mod(uint32_t a1, uint32_t a2) { return a2 == 0 ? a1 : a1%a2; }
static inline uint32_t lean_uint32_land(uint32_t a, uint32_t b) { return a & b; }
static inline uint32_t lean_uint32_lor(uint32_t a, uint32_t b) { return a | b; }
static inline uint32_t lean_uint32_xor(uint32_t a, uint32_t b) { return a ^ b; }
static inline uint32_t lean_uint32_shift_left(uint32_t a, uint32_t b) { return a << (b % 32); }
static inline uint32_t lean_uint32_shift_right(uint32_t a, uint32_t b) { return a >> (b % 32); }
static inline uint32_t lean_uint32_complement(uint32_t a) { return ~a; }
static inline uint32_t lean_uint32_log2(uint32_t a) {
    uint32_t res = 0;
    while (a >= 2) {
        res++;
        a /= 2;
    }
    return res;
}
static inline uint8_t lean_uint32_dec_eq(uint32_t a1, uint32_t a2) { return a1 == a2; }
static inline uint8_t lean_uint32_dec_lt(uint32_t a1, uint32_t a2) { return a1 < a2; }
static inline uint8_t lean_uint32_dec_le(uint32_t a1, uint32_t a2) { return a1 <= a2; }

/* UInt32 -> other */
static inline uint8_t lean_uint32_to_uint8(uint32_t a) { return ((uint8_t)a); }
static inline uint16_t lean_uint32_to_uint16(uint32_t a) { return ((uint16_t)a); }
static inline uint64_t lean_uint32_to_uint64(uint32_t a) { return ((uint64_t)a); }
static inline size_t lean_uint32_to_usize(uint32_t a) { return a; }


/* UInt64 */

LEAN_EXPORT uint64_t lean_uint64_of_big_nat(b_lean_obj_arg a);
static inline uint64_t lean_uint64_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint64_t)(lean_unbox(a)) : lean_uint64_of_big_nat(a); }
/* Remark: the following function is used to implement the constructor `UInt64.mk`. We can't annotate constructors with `@&` */
static inline uint64_t lean_uint64_of_nat_mk(lean_obj_arg a) { uint64_t r = lean_uint64_of_nat(a); lean_dec(a); return r; }
static inline uint64_t lean_uint64_add(uint64_t a1, uint64_t a2) { return a1+a2; }
static inline uint64_t lean_uint64_sub(uint64_t a1, uint64_t a2) { return a1-a2; }
static inline uint64_t lean_uint64_mul(uint64_t a1, uint64_t a2) { return a1*a2; }
static inline uint64_t lean_uint64_div(uint64_t a1, uint64_t a2) { return a2 == 0 ? 0  : a1/a2; }
static inline uint64_t lean_uint64_mod(uint64_t a1, uint64_t a2) { return a2 == 0 ? a1 : a1%a2; }
static inline uint64_t lean_uint64_land(uint64_t a, uint64_t b) { return a & b; }
static inline uint64_t lean_uint64_lor(uint64_t a, uint64_t b) { return a | b; }
static inline uint64_t lean_uint64_xor(uint64_t a, uint64_t b) { return a ^ b; }
static inline uint64_t lean_uint64_shift_left(uint64_t a, uint64_t b) { return a << (b % 64); }
static inline uint64_t lean_uint64_shift_right(uint64_t a, uint64_t b) { return a >> (b % 64); }
static inline uint64_t lean_uint64_complement(uint64_t a) { return ~a; }
static inline uint64_t lean_uint64_log2(uint64_t a) {
    uint64_t res = 0;
    while (a >= 2) {
        res++;
        a /= 2;
    }
    return res;
}
static inline uint8_t lean_uint64_dec_eq(uint64_t a1, uint64_t a2) { return a1 == a2; }
static inline uint8_t lean_uint64_dec_lt(uint64_t a1, uint64_t a2) { return a1 < a2; }
static inline uint8_t lean_uint64_dec_le(uint64_t a1, uint64_t a2) { return a1 <= a2; }
LEAN_EXPORT uint64_t lean_uint64_mix_hash(uint64_t a1, uint64_t a2);


/* UInt64 -> other */
static inline uint8_t lean_uint64_to_uint8(uint64_t a) { return ((uint8_t)a); }
static inline uint16_t lean_uint64_to_uint16(uint64_t a) { return ((uint16_t)a); }
static inline uint32_t lean_uint64_to_uint32(uint64_t a) { return ((uint32_t)a); }
static inline size_t lean_uint64_to_usize(uint64_t a) { return ((size_t)a); }

/* USize */

LEAN_EXPORT size_t lean_usize_of_big_nat(b_lean_obj_arg a);
static inline size_t lean_usize_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? lean_unbox(a) : lean_usize_of_big_nat(a); }
/* Remark: the following function is used to implement the constructor `USize.mk`. We can't annotate constructors with `@&` */
static inline size_t lean_usize_of_nat_mk(lean_obj_arg a) { size_t r = lean_usize_of_nat(a); lean_dec(a); return r; }
static inline size_t lean_usize_add(size_t a1, size_t a2) { return a1+a2; }
static inline size_t lean_usize_sub(size_t a1, size_t a2) { return a1-a2; }
static inline size_t lean_usize_mul(size_t a1, size_t a2) { return a1*a2; }
static inline size_t lean_usize_div(size_t a1, size_t a2) { return a2 == 0 ? 0  : a1/a2; }
static inline size_t lean_usize_mod(size_t a1, size_t a2) { return a2 == 0 ? a1 : a1%a2; }
static inline size_t lean_usize_land(size_t a, size_t b) { return a & b; }
static inline size_t lean_usize_lor(size_t a, size_t b) { return a | b; }
static inline size_t lean_usize_xor(size_t a, size_t b) { return a ^ b; }
static inline size_t lean_usize_shift_left(size_t a, size_t b) { return a << (b %  (sizeof(size_t) * 8)); }
static inline size_t lean_usize_shift_right(size_t a, size_t b) { return a >> (b % (sizeof(size_t) * 8)); }
static inline size_t lean_usize_complement(size_t a) { return ~a; }
static inline size_t lean_usize_log2(size_t a) {
    size_t res = 0;
    while (a >= 2) {
        res++;
        a /= 2;
    }
    return res;
}
static inline uint8_t lean_usize_dec_eq(size_t a1, size_t a2) { return a1 == a2; }
static inline uint8_t lean_usize_dec_lt(size_t a1, size_t a2) { return a1 < a2; }
static inline uint8_t lean_usize_dec_le(size_t a1, size_t a2) { return a1 <= a2; }



/* usize -> other */
static inline uint32_t lean_usize_to_uint32(size_t a) { return ((uint32_t)a); }
static inline uint64_t lean_usize_to_uint64(size_t a) { return ((uint64_t)a); }

/*
 * Note that we compile all files with -frwapv so in the following section all potential UB that
 * may arise from signed overflow is forced to match 2's complement behavior.
 *
 * We furthermore rely on the implementation defined behavior of gcc/clang to apply reduction mod
 * 2^N when casting to an integer type of size N:
 * https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html#Integers-implementation
 * Unfortunately LLVM does not yet document their implementation defined behavior but it is
 * most likely fine to rely on the fact that GCC and LLVM match on this:
 * https://github.com/llvm/llvm-project/issues/11644
 */

/* Int8 */
LEAN_EXPORT int8_t lean_int8_of_big_int(b_lean_obj_arg a);
static inline uint8_t lean_int8_of_int(b_lean_obj_arg a) {
    int8_t res;

    if (lean_is_scalar(a)) {
        res = (int8_t)lean_scalar_to_int64(a);
    } else {
        res = lean_int8_of_big_int(a);
    }

    return (uint8_t)res;
}

static inline uint8_t lean_int8_of_nat(b_lean_obj_arg a) {
    int8_t res;

    if (lean_is_scalar(a)) {
        res = (int8_t)lean_unbox(a);
    } else {
        res = lean_int8_of_big_int(a);
    }

    return (uint8_t)res;
}

static inline lean_obj_res lean_int8_to_int(uint8_t a) {
    int8_t arg = (int8_t)a;
    return lean_int64_to_int((int64_t)arg);
}

static inline uint8_t lean_int8_neg(uint8_t a) {
    int8_t arg = (int8_t)a;

    return (uint8_t)(-arg);
}

static inline uint8_t lean_int8_add(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(lhs + rhs);
}

static inline uint8_t lean_int8_sub(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(lhs - rhs);
}

static inline uint8_t lean_int8_mul(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(lhs * rhs);
}

static inline uint8_t lean_int8_div(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(rhs == 0 ? 0 : lhs / rhs);
}

static inline uint8_t lean_int8_mod(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(rhs == 0 ? lhs : lhs % rhs);
}

static inline uint8_t lean_int8_land(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(lhs & rhs);
}

static inline uint8_t lean_int8_lor(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(lhs | rhs);
}

static inline uint8_t lean_int8_xor(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return (uint8_t)(lhs ^ rhs);
}

static inline uint8_t lean_int8_shift_right(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (((int8_t)a2 % 8) + 8) % 8; // this is smod 8

    return (uint8_t)(lhs >> rhs);
}

static inline uint8_t lean_int8_shift_left(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (((int8_t)a2 % 8) + 8) % 8; // this is smod 8

    return (uint8_t)(lhs << rhs);
}

static inline uint8_t lean_int8_complement(uint8_t a) {
    int8_t arg = (int8_t)a;

    return (uint8_t)(~arg);
}

static inline uint8_t lean_int8_dec_eq(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return lhs == rhs;
}

static inline uint8_t lean_int8_dec_lt(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return lhs < rhs;
}

static inline uint8_t lean_int8_dec_le(uint8_t a1, uint8_t a2) {
    int8_t lhs = (int8_t)a1;
    int8_t rhs = (int8_t)a2;

    return lhs <= rhs;
}

/* Int8 -> other */
static inline uint16_t lean_int8_to_int16(uint8_t a) { return (uint16_t)(int16_t)(int8_t)a; }
static inline uint32_t lean_int8_to_int32(uint8_t a) { return (uint32_t)(int32_t)(int8_t)a; }
static inline uint64_t lean_int8_to_int64(uint8_t a) { return (uint64_t)(int64_t)(int8_t)a; }


/* Int16 */
LEAN_EXPORT int16_t lean_int16_of_big_int(b_lean_obj_arg a);
static inline uint16_t lean_int16_of_int(b_lean_obj_arg a) {
    int16_t res;

    if (lean_is_scalar(a)) {
        res = (int16_t)lean_scalar_to_int64(a);
    } else {
        res = lean_int16_of_big_int(a);
    }

    return (uint16_t)res;
}

static inline uint16_t lean_int16_of_nat(b_lean_obj_arg a) {
    int16_t res;

    if (lean_is_scalar(a)) {
        res = (int16_t)lean_unbox(a);
    } else {
        res = lean_int16_of_big_int(a);
    }

    return (uint16_t)res;
}

static inline lean_obj_res lean_int16_to_int(uint16_t a) {
    int16_t arg = (int16_t)a;
    return lean_int64_to_int((int64_t)arg);
}

static inline uint16_t lean_int16_neg(uint16_t a) {
    int16_t arg = (int16_t)a;

    return (uint16_t)(-arg);
}

static inline uint16_t lean_int16_add(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(lhs + rhs);
}

static inline uint16_t lean_int16_sub(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(lhs - rhs);
}

static inline uint16_t lean_int16_mul(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(lhs * rhs);
}

static inline uint16_t lean_int16_div(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(rhs == 0 ? 0 : lhs / rhs);
}

static inline uint16_t lean_int16_mod(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(rhs == 0 ? lhs : lhs % rhs);
}

static inline uint16_t lean_int16_land(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(lhs & rhs);
}

static inline uint16_t lean_int16_lor(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(lhs | rhs);
}

static inline uint16_t lean_int16_xor(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return (uint16_t)(lhs ^ rhs);
}

static inline uint16_t lean_int16_shift_right(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (((int16_t)a2 % 16) + 16) % 16; // this is smod 16

    return (uint16_t)(lhs >> rhs);
}

static inline uint16_t lean_int16_shift_left(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (((int16_t)a2 % 16) + 16) % 16; // this is smod 16

    return (uint16_t)(lhs << rhs);
}

static inline uint16_t lean_int16_complement(uint16_t a) {
    int16_t arg = (int16_t)a;

    return (uint16_t)(~arg);
}

static inline uint8_t lean_int16_dec_eq(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return lhs == rhs;
}

static inline uint8_t lean_int16_dec_lt(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return lhs < rhs;
}

static inline uint8_t lean_int16_dec_le(uint16_t a1, uint16_t a2) {
    int16_t lhs = (int16_t)a1;
    int16_t rhs = (int16_t)a2;

    return lhs <= rhs;
}

/* Int16 -> other */
static inline uint8_t lean_int16_to_int8(uint16_t a) { return (uint8_t)(int8_t)(int16_t)a; }
static inline uint32_t lean_int16_to_int32(uint16_t a) { return (uint32_t)(int32_t)(int16_t)a; }
static inline uint64_t lean_int16_to_int64(uint16_t a) { return (uint64_t)(int64_t)(int16_t)a; }

/* Int32 */
LEAN_EXPORT int32_t lean_int32_of_big_int(b_lean_obj_arg a);
static inline uint32_t lean_int32_of_int(b_lean_obj_arg a) {
    int32_t res;

    if (lean_is_scalar(a)) {
        res = (int32_t)lean_scalar_to_int64(a);
    } else {
        res = lean_int32_of_big_int(a);
    }

    return (uint32_t)res;
}

static inline uint32_t lean_int32_of_nat(b_lean_obj_arg a) {
    int32_t res;

    if (lean_is_scalar(a)) {
        res = (int32_t)lean_unbox(a);
    } else {
        res = lean_int32_of_big_int(a);
    }

    return (uint32_t)res;
}

static inline lean_obj_res lean_int32_to_int(uint32_t a) {
    int32_t arg = (int32_t)a;
    return lean_int64_to_int((int64_t)arg);
}

static inline uint32_t lean_int32_neg(uint32_t a) {
    int32_t arg = (int32_t)a;

    return (uint32_t)(-arg);
}

static inline uint32_t lean_int32_add(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(lhs + rhs);
}

static inline uint32_t lean_int32_sub(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(lhs - rhs);
}

static inline uint32_t lean_int32_mul(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(lhs * rhs);
}

static inline uint32_t lean_int32_div(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(rhs == 0 ? 0 : lhs / rhs);
}

static inline uint32_t lean_int32_mod(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(rhs == 0 ? lhs : lhs % rhs);
}

static inline uint32_t lean_int32_land(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(lhs & rhs);
}

static inline uint32_t lean_int32_lor(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(lhs | rhs);
}

static inline uint32_t lean_int32_xor(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return (uint32_t)(lhs ^ rhs);
}

static inline uint32_t lean_int32_shift_right(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (((int32_t)a2 % 32) + 32) % 32; // this is smod 32

    return (uint32_t)(lhs >> rhs);
}

static inline uint32_t lean_int32_shift_left(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (((int32_t)a2 % 32) + 32) % 32; // this is smod 32

    return (uint32_t)(lhs << rhs);
}

static inline uint32_t lean_int32_complement(uint32_t a) {
    int32_t arg = (int32_t)a;

    return (uint32_t)(~arg);
}

static inline uint8_t lean_int32_dec_eq(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return lhs == rhs;
}

static inline uint8_t lean_int32_dec_lt(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return lhs < rhs;
}

static inline uint8_t lean_int32_dec_le(uint32_t a1, uint32_t a2) {
    int32_t lhs = (int32_t)a1;
    int32_t rhs = (int32_t)a2;

    return lhs <= rhs;
}

/* Int32 -> other */
static inline uint8_t lean_int32_to_int8(uint32_t a) { return (uint8_t)(int8_t)(int32_t)a; }
static inline uint16_t lean_int32_to_int16(uint32_t a) { return (uint16_t)(int16_t)(int32_t)a; }
static inline uint64_t lean_int32_to_int64(uint32_t a) { return (uint64_t)(int64_t)(int32_t)a; }
static inline size_t lean_int32_to_isize(uint32_t a) { return (size_t)(ptrdiff_t)(int32_t)a; }

/* Int64 */
LEAN_EXPORT int64_t lean_int64_of_big_int(b_lean_obj_arg a);
static inline uint64_t lean_int64_of_int(b_lean_obj_arg a) {
    int64_t res;

    if (lean_is_scalar(a)) {
        res = lean_scalar_to_int64(a);
    } else {
        res = lean_int64_of_big_int(a);
    }

    return (uint64_t)res;
}

static inline uint64_t lean_int64_of_nat(b_lean_obj_arg a) {
    int64_t res;

    if (lean_is_scalar(a)) {
        res = (int64_t)lean_unbox(a);
    } else {
        res = lean_int64_of_big_int(a);
    }

    return (uint64_t)res;
}

static inline lean_obj_res lean_int64_to_int_sint(uint64_t a) {
    int64_t arg = (int64_t)a;
    return lean_int64_to_int(arg);
}

static inline uint64_t lean_int64_neg(uint64_t a) {
    int64_t arg = (int64_t)a;

    return (uint64_t)(-arg);
}

static inline uint64_t lean_int64_add(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(lhs + rhs);
}

static inline uint64_t lean_int64_sub(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(lhs - rhs);
}

static inline uint64_t lean_int64_mul(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(lhs * rhs);
}

static inline uint64_t lean_int64_div(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(rhs == 0 ? 0 : lhs / rhs);
}

static inline uint64_t lean_int64_mod(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(rhs == 0 ? lhs : lhs % rhs);
}

static inline uint64_t lean_int64_land(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(lhs & rhs);
}

static inline uint64_t lean_int64_lor(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(lhs | rhs);
}

static inline uint64_t lean_int64_xor(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return (uint64_t)(lhs ^ rhs);
}

static inline uint64_t lean_int64_shift_right(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (((int64_t)a2 % 64) + 64) % 64; // this is smod 64

    return (uint64_t)(lhs >> rhs);
}

static inline uint64_t lean_int64_shift_left(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (((int64_t)a2 % 64) + 64) % 64; // this is smod 64

    return (uint64_t)(lhs << rhs);
}

static inline uint64_t lean_int64_complement(uint64_t a) {
    int64_t arg = (int64_t)a;

    return (uint64_t)(~arg);
}

static inline uint8_t lean_int64_dec_eq(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return lhs == rhs;
}

static inline uint8_t lean_int64_dec_lt(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return lhs < rhs;
}

static inline uint8_t lean_int64_dec_le(uint64_t a1, uint64_t a2) {
    int64_t lhs = (int64_t)a1;
    int64_t rhs = (int64_t)a2;

    return lhs <= rhs;
}

/* Int64 -> other */
static inline uint8_t lean_int64_to_int8(uint64_t a) { return (uint8_t)(int8_t)(int64_t)a; }
static inline uint16_t lean_int64_to_int16(uint64_t a) { return (uint16_t)(int16_t)(int64_t)a; }
static inline uint32_t lean_int64_to_int32(uint64_t a) { return (uint32_t)(int32_t)(int64_t)a; }
static inline size_t lean_int64_to_isize(uint64_t a) { return (size_t)(ptrdiff_t)(int64_t)a; }

/* ISize */
LEAN_EXPORT ptrdiff_t lean_isize_of_big_int(b_lean_obj_arg a);
static inline size_t lean_isize_of_int(b_lean_obj_arg a) {
    ptrdiff_t res;

    if (lean_is_scalar(a)) {
        res = (ptrdiff_t)lean_scalar_to_int64(a);
    } else {
        res = lean_isize_of_big_int(a);
    }

    return (size_t)res;
}

static inline size_t lean_isize_of_nat(b_lean_obj_arg a) {
    ptrdiff_t res;

    if (lean_is_scalar(a)) {
        res = (ptrdiff_t)lean_unbox(a);
    } else {
        res = lean_isize_of_big_int(a);
    }

    return (size_t)res;
}

static inline lean_obj_res lean_isize_to_int(size_t a) {
    ptrdiff_t arg = (ptrdiff_t)a;
    return lean_int64_to_int((int64_t)arg);
}

static inline size_t lean_isize_neg(size_t a) {
    ptrdiff_t arg = (ptrdiff_t)a;

    return (size_t)(-arg);
}

static inline size_t lean_isize_add(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(lhs + rhs);
}

static inline size_t lean_isize_sub(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(lhs - rhs);
}

static inline size_t lean_isize_mul(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(lhs * rhs);
}

static inline size_t lean_isize_div(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(rhs == 0 ? 0 : lhs / rhs);
}

static inline size_t lean_isize_mod(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(rhs == 0 ? lhs : lhs % rhs);
}

static inline size_t lean_isize_land(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(lhs & rhs);
}

static inline size_t lean_isize_lor(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(lhs | rhs);
}

static inline size_t lean_isize_xor(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return (size_t)(lhs ^ rhs);
}

static inline size_t lean_isize_shift_right(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t size = sizeof(ptrdiff_t) * 8;
    ptrdiff_t rhs = (((ptrdiff_t)a2 % size) + size) % size; // this is smod

    return (size_t)(lhs >> rhs);
}

static inline size_t lean_isize_shift_left(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t size = sizeof(ptrdiff_t) * 8;
    ptrdiff_t rhs = (((ptrdiff_t)a2 % size) + size) % size; // this is smod

    return (size_t)(lhs << rhs);
}

static inline size_t lean_isize_complement(size_t a) {
    ptrdiff_t arg = (ptrdiff_t)a;

    return (size_t)(~arg);
}

static inline uint8_t lean_isize_dec_eq(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return lhs == rhs;
}

static inline uint8_t lean_isize_dec_lt(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return lhs < rhs;
}

static inline uint8_t lean_isize_dec_le(size_t a1, size_t a2) {
    ptrdiff_t lhs = (ptrdiff_t)a1;
    ptrdiff_t rhs = (ptrdiff_t)a2;

    return lhs <= rhs;
}

/* ISize -> other */
static inline uint32_t lean_isize_to_int32(size_t a) { return (uint32_t)(int32_t)(ptrdiff_t)a; }
static inline uint64_t lean_isize_to_int64(size_t a) { return (uint64_t)(int64_t)(ptrdiff_t)a; }

/* Float */

LEAN_EXPORT lean_obj_res lean_float_to_string(double a);
LEAN_EXPORT double lean_float_scaleb(double a, b_lean_obj_arg b);
LEAN_EXPORT uint8_t lean_float_isnan(double a);
LEAN_EXPORT uint8_t lean_float_isfinite(double a);
LEAN_EXPORT uint8_t lean_float_isinf(double a);
LEAN_EXPORT lean_obj_res lean_float_frexp(double a);

/* Boxing primitives */

static inline lean_obj_res lean_box_uint32(uint32_t v) {
    if (sizeof(void*) == 4) {
        /* 32-bit implementation */
        lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(uint32_t));
        lean_ctor_set_uint32(r, 0, v);
        return r;
    } else {
        /* 64-bit implementation */
        return lean_box(v);
    }
}

static inline unsigned lean_unbox_uint32(b_lean_obj_arg o) {
    if (sizeof(void*) == 4) {
        /* 32-bit implementation */
        return lean_ctor_get_uint32(o, 0);
    } else {
        /* 64-bit implementation */
        return lean_unbox(o);
    }
}

static inline lean_obj_res lean_box_uint64(uint64_t v) {
    lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(uint64_t));
    lean_ctor_set_uint64(r, 0, v);
    return r;
}

static inline uint64_t lean_unbox_uint64(b_lean_obj_arg o) {
    return lean_ctor_get_uint64(o, 0);
}

static inline lean_obj_res lean_box_usize(size_t v) {
    lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(size_t));
    lean_ctor_set_usize(r, 0, v);
    return r;
}

static inline size_t lean_unbox_usize(b_lean_obj_arg o) {
    return lean_ctor_get_usize(o, 0);
}

static inline lean_obj_res lean_box_float(double v) {
    lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(double)); // NOLINT
    lean_ctor_set_float(r, 0, v);
    return r;
}

static inline double lean_unbox_float(b_lean_obj_arg o) {
    return lean_ctor_get_float(o, 0);
}

/* Debugging helper functions */

LEAN_EXPORT lean_object * lean_dbg_trace(lean_obj_arg s, lean_obj_arg fn);
LEAN_EXPORT lean_object * lean_dbg_sleep(uint32_t ms, lean_obj_arg fn);
LEAN_EXPORT lean_object * lean_dbg_trace_if_shared(lean_obj_arg s, lean_obj_arg a);

/* IO Helper functions */

LEAN_EXPORT lean_obj_res lean_decode_io_error(int errnum, b_lean_obj_arg fname);
LEAN_EXPORT lean_obj_res lean_decode_uv_error(int errnum, b_lean_obj_arg fname);

static inline lean_obj_res lean_io_mk_world() { return lean_box(0); }
static inline bool lean_io_result_is_ok(b_lean_obj_arg r) { return lean_ptr_tag(r) == 0; }
static inline bool lean_io_result_is_error(b_lean_obj_arg r) { return lean_ptr_tag(r) == 1; }
static inline b_lean_obj_res lean_io_result_get_value(b_lean_obj_arg r) { assert(lean_io_result_is_ok(r)); return lean_ctor_get(r, 0); }
static inline b_lean_obj_res lean_io_result_get_error(b_lean_obj_arg r) { assert(lean_io_result_is_error(r)); return lean_ctor_get(r, 0); }
LEAN_EXPORT void lean_io_result_show_error(b_lean_obj_arg r);
LEAN_EXPORT void lean_io_mark_end_initialization(void);
static inline lean_obj_res lean_io_result_mk_ok(lean_obj_arg a) {
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, lean_box(0));
    return r;
}
static inline lean_obj_res lean_io_result_mk_error(lean_obj_arg e) {
    lean_object * r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(r, 0, e);
    lean_ctor_set(r, 1, lean_box(0));
    return r;
}

LEAN_EXPORT lean_obj_res lean_mk_io_error_already_exists(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_already_exists_file(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_eof(lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_hardware_fault(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_illegal_operation(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_inappropriate_type(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_inappropriate_type_file(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_interrupted(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_invalid_argument(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_invalid_argument_file(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_no_file_or_directory(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_no_such_thing(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_no_such_thing_file(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_other_error(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_permission_denied(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_permission_denied_file(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_protocol_error(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_resource_busy(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_resource_exhausted(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_resource_exhausted_file(lean_obj_arg, uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_resource_vanished(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_time_expired(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_unsatisfied_constraints(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_error_unsupported_operation(uint32_t, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_mk_io_user_error(lean_obj_arg str);


/* ST Ref primitives */
LEAN_EXPORT lean_obj_res lean_st_mk_ref(lean_obj_arg, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_st_ref_get(b_lean_obj_arg, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_st_ref_set(b_lean_obj_arg, lean_obj_arg, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_st_ref_reset(b_lean_obj_arg, lean_obj_arg);
LEAN_EXPORT lean_obj_res lean_st_ref_swap(b_lean_obj_arg, lean_obj_arg, lean_obj_arg);

/* pointer address unsafe primitive  */
static inline size_t lean_ptr_addr(b_lean_obj_arg a) { return (size_t)a; }

/* Name primitives */
LEAN_EXPORT uint8_t lean_name_eq(b_lean_obj_arg n1, b_lean_obj_arg n2);

static inline uint64_t lean_name_hash_ptr(b_lean_obj_arg n) {
    assert(!lean_is_scalar(n));
    return lean_ctor_get_uint64(n, sizeof(lean_object*)*2);
}

static inline uint64_t lean_name_hash(b_lean_obj_arg n) {
    if (lean_is_scalar(n))
        return 1723;
    else
        return lean_name_hash_ptr(n);
}

/* float primitives */
static inline uint8_t lean_float_to_uint8(double a) {
    return 0. <= a ? (a < 256. ? (uint8_t)a : UINT8_MAX) : 0;
}
static inline uint16_t lean_float_to_uint16(double a) {
    return 0. <= a ? (a < 65536. ? (uint16_t)a : UINT16_MAX) : 0;
}
static inline uint32_t lean_float_to_uint32(double a) {
    return 0. <= a ? (a < 4294967296. ? (uint32_t)a : UINT32_MAX) : 0;
}
static inline uint64_t lean_float_to_uint64(double a) {
    return 0. <= a ? (a < 18446744073709551616. ? (uint64_t)a : UINT64_MAX) : 0;
}
static inline size_t lean_float_to_usize(double a) {
    if (sizeof(size_t) == sizeof(uint64_t)) // NOLINT
        return (size_t) lean_float_to_uint64(a); // NOLINT
    else
        return (size_t) lean_float_to_uint32(a); // NOLINT
}
static inline double lean_float_add(double a, double b) { return a + b; }
static inline double lean_float_sub(double a, double b) { return a - b; }
static inline double lean_float_mul(double a, double b) { return a * b; }
static inline double lean_float_div(double a, double b) { return a / b; }
static inline double lean_float_negate(double a) { return -a; }
static inline uint8_t lean_float_beq(double a, double b) { return a == b; }
static inline uint8_t lean_float_decLe(double a, double b) { return a <= b; }
static inline uint8_t lean_float_decLt(double a, double b) { return a < b; }
static inline double lean_uint64_to_float(uint64_t a) { return (double) a; }

/* Efficient C implementations of defns used by the compiler */
static inline size_t lean_hashmap_mk_idx(lean_obj_arg sz, uint64_t hash) {
    return (size_t)(hash & (lean_unbox(sz) - 1));
}

static inline size_t lean_hashset_mk_idx(lean_obj_arg sz, uint64_t hash) {
    return (size_t)(hash & (lean_unbox(sz) - 1));
}

static inline uint64_t lean_expr_data(lean_obj_arg expr) {
    return lean_ctor_get_uint64(expr, lean_ctor_num_objs(expr)*sizeof(void*));
}

// eliding unused parameter names is C23+, so ignore warning instead in the following
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

static inline lean_obj_res lean_get_max_ctor_fields(lean_obj_arg _unit) {
    return lean_box(LEAN_MAX_CTOR_FIELDS);
}

static inline lean_obj_res lean_get_max_ctor_scalars_size(lean_obj_arg _unit) {
    return lean_box(LEAN_MAX_CTOR_SCALARS_SIZE);
}

static inline lean_obj_res lean_get_usize_size(lean_obj_arg _unit) {
    return lean_box(sizeof(size_t));
}

static inline lean_obj_res lean_get_max_ctor_tag(lean_obj_arg _unit) {
    return lean_box(LeanMaxCtorTag);
}

static inline uint8_t lean_strict_or(uint8_t b1, uint8_t b2) {
    return b1 || b2;
}

static inline uint8_t lean_strict_and(uint8_t b1, uint8_t b2) {
    return b1 && b2;
}

static inline lean_obj_res lean_version_get_major(lean_obj_arg _unit) {
    return lean_box(LEAN_VERSION_MAJOR);
}

static inline lean_obj_res lean_version_get_minor(lean_obj_arg _unit) {
    return lean_box(LEAN_VERSION_MINOR);
}

static inline lean_obj_res lean_version_get_patch(lean_obj_arg _unit) {
    return lean_box(LEAN_VERSION_PATCH);
}

static inline uint8_t lean_version_get_is_release(lean_obj_arg _unit) {
    return LEAN_VERSION_IS_RELEASE;
}

static inline lean_obj_res lean_version_get_special_desc(lean_obj_arg _unit) {
    return lean_mk_string(LEAN_SPECIAL_VERSION_DESC);
}

static inline lean_obj_res lean_system_platform_target(lean_obj_arg _unit) {
    return lean_mk_string(LEAN_PLATFORM_TARGET);
}

static inline uint8_t lean_internal_is_stage0(lean_obj_arg _unit) {
    return LEAN_IS_STAGE0;
}

static inline lean_obj_res lean_nat_pred(b_lean_obj_arg n) {
    return lean_nat_sub(n, lean_box(1));
}

static inline lean_obj_res lean_runtime_mark_multi_threaded(lean_obj_arg a) {
    lean_mark_mt(a);
    return a;
}

static inline lean_obj_res lean_runtime_mark_persistent(lean_obj_arg a) {
    lean_mark_persistent(a);
    return a;
}

#ifdef __cplusplus
}
#endif
