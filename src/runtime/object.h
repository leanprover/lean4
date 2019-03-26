/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include <cstdlib>
#if !defined(__APPLE__)
#include <malloc.h>
#endif
#include "runtime/compiler_hints.h"
#include "runtime/mpz.h"
#include "runtime/int64.h"
#include "runtime/thread.h"

#ifdef _MSC_VER
#define LEAN_ALLOCA(s) ::_alloca(s)
#else
#define LEAN_ALLOCA(s) ::alloca(s)
#endif

namespace lean {
typedef unsigned char      uint8;
typedef unsigned short     uint16;
typedef unsigned           uint32;
typedef unsigned long long uint64;
typedef size_t             usize;

#ifdef LEAN_RUNTIME_STATS
#define LEAN_RUNTIME_STAT_CODE(c) c
extern atomic<uint64> g_num_ctor;
extern atomic<uint64> g_num_closure;
extern atomic<uint64> g_num_string;
extern atomic<uint64> g_num_array;
extern atomic<uint64> g_num_thunk;
extern atomic<uint64> g_num_task;
extern atomic<uint64> g_num_ext;
extern atomic<uint64> g_num_st_inc;
extern atomic<uint64> g_num_mt_inc;
extern atomic<uint64> g_num_st_dec;
extern atomic<uint64> g_num_mt_dec;
extern atomic<uint64> g_num_del;
#else
#define LEAN_RUNTIME_STAT_CODE(c)
#endif

/* Objects can be stored in 5 different kinds of memory:
   - `MTHeap`: multi-threaded heap, the reference counter (RC) is updated using atomic operations.
      All objects reachable from an object in the `MTHeap` are in `MTHeap`, `Persistent` or `Region`.
   - `STHeap`: single-threaded heap, the RC is faster to update.
      All objects reachable from an object in the `STHeap` are not in the `Stack`.
   - `Persistent`: RC is never updated, this kind of object is never garbage collected.
      All objects reachable from a persistent object are not in the `Stack`.
   - `Stack`: object does not have a RC and is allocated on the system stack.
   - `Region`: object does not have a RC, and is stored in a compacted region.
      All objects reachable from an object in a compacted region are also in the same compacted region.
*/
enum class object_memory_kind { MTHeap = 0, STHeap, Persistent, Stack, Region };

enum class object_kind { Constructor, Closure, Array, ScalarArray,
                         PArrayRoot, PArraySet, PArrayPush, PArrayPop,
                         String, MPZ, Thunk, Task, Ref, External };

/* Objects are initially allocated as STHeap. When we create a task, we change it to MTHeap. */
constexpr object_memory_kind c_init_mem_kind = object_memory_kind::STHeap;

/* The reference counter is a uintptr_t, because at deletion time, we use this field to implement
   a linked list of objects to be deleted. */
typedef uintptr_t rc_type;

/* Base class for all runtime objects.

   \remark If m_mem_kind == STHeap/MTHeap, then we store the reference counter before the object. */
struct object {
    unsigned        m_kind:8;
    unsigned        m_mem_kind:8;
    object(object_kind k, object_memory_kind m = c_init_mem_kind):
        m_kind(static_cast<unsigned>(k)), m_mem_kind(static_cast<unsigned>(m)) {}
};

/* We can represent inductive datatypes that have:
   1) At most 2^16 constructors
   2) At most 2^16 - 1 object fields per constructor
   3) At most 2^16 - 1 bytes for scalar/unboxed fields

   We only need m_scalar_size for implementing sanity checks at runtime.

   Header size: 12 bytes in 32 bit machines and 16 bytes in 64 bit machines. */
struct constructor_object : public object {
    unsigned short m_tag;
    unsigned short m_num_objs;
    unsigned short m_scalar_size;
    constructor_object(unsigned tag, unsigned num_objs, unsigned scalar_sz, object_memory_kind m = c_init_mem_kind):
        object(object_kind::Constructor, m), m_tag(tag), m_num_objs(num_objs), m_scalar_size(scalar_sz) {}
};

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
typedef object * obj_arg;   /* Standard object argument. */
typedef object * b_obj_arg; /* Borrowed object argument. */
typedef object * u_obj_arg; /* Unique (aka non shared) object argument. */
typedef object * obj_res;   /* Standard object result. */
typedef object * b_obj_res; /* Borrowed object result. */

/* Array of objects.
   Header size: 16 bytes in 32 bit machines and 32 bytes in 64 bit machines. */
struct array_object : public object {
    size_t   m_size;
    size_t   m_capacity;
    array_object(size_t sz, size_t c, object_memory_kind m = c_init_mem_kind):
        object(object_kind::Array, m), m_size(sz), m_capacity(c) {}
};

/* Array of scalar values.
   We support arrays with upto 2^64 elements in 64 bit machines.

   The field m_elem_size is only needed for implementing sanity checks at runtime.
   Header size: 16 bytes in 32 bit machines and 32 bytes in 64 bit machines. */
struct sarray_object : public object {
    unsigned m_elem_size:16; // in bytes
    size_t   m_size;
    size_t   m_capacity;
    sarray_object(unsigned esz, size_t sz, size_t c, object_memory_kind m = c_init_mem_kind):
        object(object_kind::ScalarArray, m), m_elem_size(esz), m_size(sz), m_capacity(c) {}
};

struct string_object : public object {
    size_t m_size;
    size_t m_capacity;
    size_t m_length;   // UTF8 length
    string_object(size_t sz, size_t c, size_t len, object_memory_kind m = c_init_mem_kind):
        object(object_kind::String, m), m_size(sz), m_capacity(c), m_length(len) {}
};

/* Persistent arrays are implemented using 4 different kinds of cell:
   PArraySet, PArrayPush, PArrayPop and PArrayRoot. */
struct parray_object : public object {
    parray_object * m_next; // PArraySet, PArrayPush, PArrayPop
    union {
        size_t   m_idx;  // PArraySet
        size_t   m_size; // PArrayRoot
    };
    union {
        object ** m_data; // PArrayRoot
        object *  m_elem; // PArrayPush and PArraySet
    };
    /* Remark: persistent arrays are single threaded object. The `mark_shared` operation
       copies it when the RC > 1 */
    parray_object():object(object_kind::PArrayRoot, object_memory_kind::STHeap) {}
};

/* Note that `m_fun` is a pointer to a C function.
   The `apply` operator performs a cast operation. It casts m_fun to a C function pointer of the right arity.

   Header size: 16 bytes in 32 bit machines and 24 bytes in 64 bit machines.

   Note that this structure may also be used to simulate closures built
   from bytecodes. We just store an extra argument: the virtual machine
   function descriptor. We store in m_fun a pointer to a C function
   that extracts the function descriptor and then invokes the VM. */
struct closure_object : public object {
    unsigned  m_arity:16;     // number of arguments expected by m_fun.
    unsigned  m_num_fixed:16; // number of arguments that have been already fixed.
    void *    m_fun;
    closure_object(void * f, unsigned arity, unsigned n, object_memory_kind m = c_init_mem_kind):
        object(object_kind::Closure, m), m_arity(arity), m_num_fixed(n), m_fun(f) {}
};

struct mpz_object : public object {
    mpz m_value;
    mpz_object(mpz const & v, object_memory_kind m = c_init_mem_kind):
        object(object_kind::MPZ, m), m_value(v) {}
};

struct ref_object : public object {
    object * m_value;
    ref_object(object * v, object_memory_kind m = c_init_mem_kind):
        object(object_kind::Ref, m), m_value(v) {
    };
};

struct thunk_object : public object {
    atomic<object *> m_value;
    atomic<object *> m_closure;
    thunk_object(object * c, bool is_value = false, object_memory_kind m = c_init_mem_kind);
};

struct task_object : public object {
    /* Data required for executing a task. It is released as soon as
       the task terminates. */
    struct imp {
        object *              m_closure;
        task_object *         m_head_dep{nullptr};  /* head of the reverse dependency list of this task. */
        task_object *         m_next_dep{nullptr};  /* next element in the reverse dependency list. Each task can be in at most one reverse dependency list. */
        unsigned              m_prio;
        bool                  m_interrupted{false};
        bool                  m_deleted{false};
        imp(object * c, unsigned prio):m_closure(c), m_prio(prio) {}
    };
    atomic<object *>          m_value;
    imp *                     m_imp;
    task_object(object * c, unsigned prio);
    task_object(object * v);
};

struct external_object_class;
typedef void (*external_object_finalize_proc)(void *);
typedef void (*external_object_foreach_proc)(void *, b_obj_arg);
external_object_class * register_external_object_class(external_object_finalize_proc, external_object_foreach_proc);

/* Object for wrapping external data.
   For example, we use it to wrap the Lean environment object. */
struct external_object : public object {
    external_object_class * m_class;
    void *                  m_data;
    explicit external_object(external_object_class * cls, void * data, object_memory_kind m = c_init_mem_kind):
        object(object_kind::External, m), m_class(cls), m_data(data) {}
};

static_assert(sizeof(size_t) == sizeof(void*), "runtime assumes that size_t and void* have the same size, we do not plan to support old platforms where this is not true");

inline bool is_null(object * o) { return o == nullptr; }
inline bool is_scalar(object * o) { return (reinterpret_cast<size_t>(o) & 1) == 1; }
inline object * box(size_t n) { return reinterpret_cast<object*>((static_cast<size_t>(n) << 1) | 1); }
inline size_t unbox(object * o) { return reinterpret_cast<size_t>(o) >> 1; }

/* Generic Lean object delete operation.

   The generic delete must be used when we are compiling:
   1- Polymorphic code.
   2- Code using `any` type.
      The `any` type is introduced when we translate Lean expression into the Core language based on System-F.

   We are planning to generate delete operations for non-polymorphic code.
   They can be faster because:
   1- They do not need to test whether nested pointers are boxed scalars or not.
   2- They do not need to test the kind.
   3- They can unfold the loop that decrements the reference counters for nested objects.

   \pre !is_scalar(o); */
void del(object * o);

static_assert(sizeof(atomic<rc_type>) == sizeof(rc_type),  "atomic<rc_type> and rc_type must have the same size"); // NOLINT

void * alloc_heap_object(size_t sz);
void free_heap_obj(object * o);
void free_mpz_obj(object * o);
void free_closure_obj(object * o);

inline atomic<rc_type> * mt_rc_addr(object * o) {
    return reinterpret_cast<atomic<rc_type> *>(reinterpret_cast<char *>(o) - sizeof(rc_type));
}

inline rc_type * st_rc_addr(object * o) {
    return reinterpret_cast<rc_type *>(reinterpret_cast<char *>(o) - sizeof(rc_type));
}

inline rc_type & st_rc_ref(object * o) {
    return *st_rc_addr(o);
}

inline bool is_mt_heap_obj(object * o) {
#ifdef LEAN_MULTI_THREAD
    return o->m_mem_kind == static_cast<unsigned>(object_memory_kind::MTHeap);
#else
    return false;
#endif
}
inline bool is_st_heap_obj(object * o) { return o->m_mem_kind == static_cast<unsigned>(object_memory_kind::STHeap); }
inline bool is_heap_obj(object * o) { return is_st_heap_obj(o) || is_mt_heap_obj(o); }
void mark_mt(object * o);

inline rc_type get_rc(object * o) {
    lean_assert(!is_scalar(o));
    if (LEAN_LIKELY(is_st_heap_obj(o))) {
        return st_rc_ref(o);
    } else {
        lean_assert(is_mt_heap_obj(o));
        return atomic_load_explicit(mt_rc_addr(o), memory_order_acquire);
    }
}

inline bool is_shared(object * o) { return get_rc(o) > 1; }
inline bool is_exclusive(object * o) { return is_heap_obj(o) && !is_shared(o); }

inline void inc_ref(object * o) {
    if (LEAN_LIKELY(is_st_heap_obj(o))) {
        LEAN_RUNTIME_STAT_CODE(g_num_st_inc++);
        st_rc_ref(o)++;
    } else if (is_mt_heap_obj(o)) {
        LEAN_RUNTIME_STAT_CODE(g_num_mt_inc++);
        atomic_fetch_add_explicit(mt_rc_addr(o), static_cast<rc_type>(1), memory_order_relaxed);
    }
}

inline void inc_ref(object * o, rc_type n) {
    if (LEAN_LIKELY(is_st_heap_obj(o))) {
        LEAN_RUNTIME_STAT_CODE(g_num_st_inc++);
        st_rc_ref(o) += n;
    } else if (is_mt_heap_obj(o)) {
        LEAN_RUNTIME_STAT_CODE(g_num_mt_inc++);
        atomic_fetch_add_explicit(mt_rc_addr(o), static_cast<rc_type>(n), memory_order_relaxed);
    }
}

inline void dec_shared_ref(object * o) {
    lean_assert(is_shared(o));
    if (LEAN_LIKELY(is_st_heap_obj(o))) {
        LEAN_RUNTIME_STAT_CODE(g_num_st_dec++);
        st_rc_ref(o)--;
    } else if (is_mt_heap_obj(o)) {
        LEAN_RUNTIME_STAT_CODE(g_num_mt_dec++);
        atomic_fetch_sub_explicit(mt_rc_addr(o), static_cast<rc_type>(1), memory_order_acq_rel);
    }
}

inline bool dec_ref_core(object * o) {
    if (LEAN_LIKELY(is_st_heap_obj(o))) {
        lean_assert(get_rc(o) > 0);
        LEAN_RUNTIME_STAT_CODE(g_num_st_dec++);
        st_rc_ref(o)--;
        return st_rc_ref(o) == 0;
    } else if (is_mt_heap_obj(o)) {
        lean_assert(get_rc(o) > 0);
        LEAN_RUNTIME_STAT_CODE(g_num_mt_dec++);
        return atomic_fetch_sub_explicit(mt_rc_addr(o), static_cast<rc_type>(1), memory_order_acq_rel) == 1;
    } else {
        return false;
    }
}

inline void dec_ref(object * o) { if (dec_ref_core(o)) del(o); }
inline void inc(object * o) { if (!is_scalar(o)) inc_ref(o); }
inline void inc(object * o, rc_type n) { if (!is_scalar(o)) inc_ref(o, n); }
inline void dec(object * o) { if (!is_scalar(o)) dec_ref(o); }

// =======================================
// Testers

inline object_kind get_kind(object * o) { return static_cast<object_kind>(o->m_kind); }
inline bool is_cnstr(object * o) { return get_kind(o) == object_kind::Constructor; }
inline bool is_closure(object * o) { return get_kind(o) == object_kind::Closure; }
inline bool is_array(object * o) { return get_kind(o) == object_kind::Array; }
inline bool is_sarray(object * o) { return get_kind(o) == object_kind::ScalarArray; }
inline bool is_parray(object * o) { auto k = get_kind(o); return k == object_kind::PArrayRoot || k == object_kind::PArraySet || k == object_kind::PArrayPush || k == object_kind::PArrayPop; }
inline bool is_string(object * o) { return get_kind(o) == object_kind::String; }
inline bool is_mpz(object * o) { return get_kind(o) == object_kind::MPZ; }
inline bool is_thunk(object * o) { return get_kind(o) == object_kind::Thunk; }
inline bool is_task(object * o) { return get_kind(o) == object_kind::Task; }
inline bool is_external(object * o) { return get_kind(o) == object_kind::External; }
inline bool is_ref(object * o) { return get_kind(o) == object_kind::Ref; }

// =======================================
// Casting

inline constructor_object * to_cnstr(object * o) { lean_assert(is_cnstr(o)); return static_cast<constructor_object*>(o); }
inline closure_object * to_closure(object * o) { lean_assert(is_closure(o)); return static_cast<closure_object*>(o); }
inline array_object * to_array(object * o) { lean_assert(is_array(o)); return static_cast<array_object*>(o); }
inline sarray_object * to_sarray(object * o) { lean_assert(is_sarray(o)); return static_cast<sarray_object*>(o); }
inline parray_object * to_parray(object * o) { lean_assert(is_parray(o)); return static_cast<parray_object*>(o); }
inline string_object * to_string(object * o) { lean_assert(is_string(o)); return static_cast<string_object*>(o); }
inline mpz_object * to_mpz(object * o) { lean_assert(is_mpz(o)); return static_cast<mpz_object*>(o); }
inline thunk_object * to_thunk(object * o) { lean_assert(is_thunk(o)); return static_cast<thunk_object*>(o); }
inline task_object * to_task(object * o) { lean_assert(is_task(o)); return static_cast<task_object*>(o); }
inline ref_object * to_ref(object * o) { lean_assert(is_ref(o)); return static_cast<ref_object*>(o); }
inline external_object * to_external(object * o) { lean_assert(is_external(o)); return static_cast<external_object*>(o); }

/* The memory associated with all Lean objects but `mpz_object` and `external_object` can be deallocated using `free`.
   All fields in these objects are integral types, but the reference counter.
   However, `std::atomic<Integral>` has a trivial destructor.
   In the C++ reference manual (http://en.cppreference.com/w/cpp/atomic/atomic), we find the following sentence:

   "Additionally, the resulting std::atomic<Integral> specialization has standard layout, a trivial default constructor,
   and a trivial destructor." */
inline void dealloc_mpz(object * o) { to_mpz(o)->~mpz_object(); free_mpz_obj(o); }
inline void dealloc(object * o) {
    lean_assert(is_heap_obj(o));
    switch (get_kind(o)) {
    case object_kind::MPZ:      dealloc_mpz(o); break;
    case object_kind::Task:     lean_unreachable(); // only the task manager can deallocate tasks.
    default: free_heap_obj(o); break;
    }
}

// =======================================
// Object auxiliary functions

/* Size of the object in bytes. This function is used for debugging purposes.
   \pre !is_scalar(o) */
size_t obj_byte_size(object * o);

/* Size of the object header in bytes. This function is used for debugging purposes.
   \pre !is_scalar(o) */
size_t obj_header_size(object * o);

/* Retrieves data of type `T` stored offset bytes inside of `o` */
template<typename T>
inline T obj_data(object * o, size_t offset) {
    lean_assert(obj_header_size(o) <= offset);
    lean_assert(offset + sizeof(T) <= obj_byte_size(o));
    return *(reinterpret_cast<T *>(reinterpret_cast<char *>(o) + offset));
}

/* Set object data of type T */
template<typename T>
inline void obj_set_data(object * o, size_t offset, T v) {
    lean_assert(!is_heap_obj(o) || !is_shared(o));
    lean_assert(obj_header_size(o) <= offset);
    lean_assert(offset + sizeof(T) <= obj_byte_size(o));
    *(reinterpret_cast<T *>(reinterpret_cast<char *>(o) + offset)) = v;
}

/* Mark all objects reachable from `o` as persistent */
void mark_persistent(object * o);

// =======================================
// Constructor auxiliary functions

inline unsigned cnstr_num_objs(object * o) { return to_cnstr(o)->m_num_objs; }
inline unsigned cnstr_scalar_size(object * o) { return to_cnstr(o)->m_scalar_size; }
inline size_t cnstr_byte_size(unsigned num_objs, unsigned scalar_sz) { return sizeof(constructor_object) + num_objs*sizeof(object*) + scalar_sz; } // NOLINT
inline size_t cnstr_byte_size(object * o) { return cnstr_byte_size(cnstr_num_objs(o), cnstr_scalar_size(o)); }
inline object ** cnstr_obj_cptr(object * o) {
    lean_assert(is_cnstr(o));
    return reinterpret_cast<object**>(reinterpret_cast<char*>(o) + sizeof(constructor_object));
}
inline unsigned char * cnstr_scalar_cptr(object * o) {
    lean_assert(is_cnstr(o));
    return reinterpret_cast<unsigned char*>(reinterpret_cast<char*>(o) + sizeof(constructor_object) + cnstr_num_objs(o)*sizeof(object*)); // NOLINT
}

// =======================================
// Closure auxiliary functions

inline void * closure_fun(object * o) { return to_closure(o)->m_fun; }
inline unsigned closure_arity(object * o) { return to_closure(o)->m_arity; }
inline unsigned closure_num_fixed(object * o) { return to_closure(o)->m_num_fixed; }
inline size_t closure_byte_size(unsigned num_fixed) { return sizeof(closure_object) + num_fixed*sizeof(object*); } // NOLINT
inline size_t closure_byte_size(object * o) { return closure_byte_size(closure_num_fixed(o)); }
inline object ** closure_arg_cptr(object * o) {
    lean_assert(is_closure(o));
    return reinterpret_cast<object**>(reinterpret_cast<char*>(o) + sizeof(closure_object));
}

// =======================================
// Thunk auxiliary functions

inline thunk_object::thunk_object(object * c, bool is_value, object_memory_kind m):
    object(object_kind::Thunk, m) {
    if (is_value) {
        m_closure = nullptr;
        m_value   = c;
    } else {
        lean_assert(is_closure(c));
        m_closure = c;
        m_value   = nullptr;
    }
}
object * apply_1(object * f, object * a1);
/* Expensive version of thunk_get which tries to execute the nested closure */
object * thunk_get_core(object * t);

// =======================================
// Array auxiliary functions

inline size_t array_capacity(object * o) { return to_array(o)->m_capacity; }
inline size_t array_byte_size(size_t capacity) { return sizeof(array_object) + capacity*sizeof(object*); } // NOLINT
inline size_t array_byte_size(object * o) { return array_byte_size(array_capacity(o)); }
inline object ** array_cptr(object * o) {
    lean_assert(is_array(o));
    return reinterpret_cast<object**>(reinterpret_cast<char*>(o) + sizeof(array_object));
}

// =======================================
// Array of scalars auxiliary functions

inline unsigned sarray_elem_size(object * o) { return to_sarray(o)->m_elem_size; }
inline size_t sarray_capacity(object * o) { return to_sarray(o)->m_capacity; }
inline size_t sarray_byte_size(size_t capacity, unsigned elem_size) { return sizeof(sarray_object) + capacity*elem_size; } // NOLINT
inline size_t sarray_byte_size(object * o) { return sarray_byte_size(sarray_capacity(o), sarray_elem_size(o)); }
template<typename T>
T * sarray_cptr_core(object * o) { lean_assert(is_sarray(o)); return reinterpret_cast<T*>(reinterpret_cast<char*>(o) + sizeof(sarray_object)); }
template<typename T>
T * sarray_cptr(object * o) { lean_assert(sarray_elem_size(o) == sizeof(T)); return sarray_cptr_core<T>(o); }

// =======================================
// String auxiliary functions

inline size_t string_capacity(object * o) { return to_string(o)->m_capacity; }
inline size_t string_byte_size(size_t capacity) { return sizeof(string_object) + capacity; } // NOLINT
inline size_t string_byte_size(object * o) { return string_byte_size(string_capacity(o)); }

// =======================================
// MPZ auxiliary function

inline object * alloc_mpz(mpz const & m) { return new (alloc_heap_object(sizeof(mpz_object))) mpz_object(m); }

// =======================================
// External objects

inline object * alloc_external(external_object_class * cls, void * data) {
    LEAN_RUNTIME_STAT_CODE(g_num_ext++);
    return new (alloc_heap_object(sizeof(external_object))) external_object(cls, data);
}

inline external_object_class * external_class(object * o) { return to_external(o)->m_class; }
inline void * external_data(object * o) { return to_external(o)->m_data; }

// =======================================
// Natural numbers auxiliary functions

#define LEAN_MAX_SMALL_NAT (std::numeric_limits<size_t>::max() >> 1) // NOLINT
inline object * mk_nat_obj_core(mpz const & m) {
    lean_assert(m > LEAN_MAX_SMALL_NAT);
    return alloc_mpz(m);
}
object * nat_big_add(object * a1, object * a2);
object * nat_big_sub(object * a1, object * a2);
object * nat_big_mul(object * a1, object * a2);
object * nat_big_div(object * a1, object * a2);
object * nat_big_mod(object * a1, object * a2);
bool nat_big_eq(object * a1, object * a2);
bool nat_big_le(object * a1, object * a2);
bool nat_big_lt(object * a1, object * a2);
object * nat_big_land(object * a1, object * a2);
object * nat_big_lor(object * a1, object * a2);
object * nat_big_xor(object * a1, object * a2);

// =======================================
// Integers auxiliary functions

#define LEAN_MAX_SMALL_INT (sizeof(void*) == 8 ? std::numeric_limits<int>::max() : (1 << 30)) // NOLINT
#define LEAN_MIN_SMALL_INT (sizeof(void*) == 8 ? std::numeric_limits<int>::min() : -(1 << 30)) // NOLINT
inline object * mk_int_obj_core(mpz const & m) {
    lean_assert(m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT);
    return alloc_mpz(m);
}
object * int_big_add(object * a1, object * a2);
object * int_big_sub(object * a1, object * a2);
object * int_big_mul(object * a1, object * a2);
object * int_big_div(object * a1, object * a2);
object * int_big_mod(object * a1, object * a2);
bool int_big_eq(object * a1, object * a2);
bool int_big_le(object * a1, object * a2);
bool int_big_lt(object * a1, object * a2);

// =======================================
// Constructor objects
inline obj_res alloc_cnstr(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    LEAN_RUNTIME_STAT_CODE(g_num_ctor++);
    lean_assert(tag < 65536 && num_objs < 65536 && scalar_sz < 65536);
    return new (alloc_heap_object(cnstr_byte_size(num_objs, scalar_sz))) constructor_object(tag, num_objs, scalar_sz); // NOLINT
}
inline unsigned cnstr_tag(b_obj_arg o) { return to_cnstr(o)->m_tag; }
inline void cnstr_set_tag(b_obj_arg o, unsigned tag) { to_cnstr(o)->m_tag = tag; }
/* Access constructor object field `i` */
inline b_obj_res cnstr_get(b_obj_arg o, unsigned i) {
    lean_assert(i < cnstr_num_objs(o));
    return obj_data<object*>(o, sizeof(constructor_object) + sizeof(object*)*i); // NOLINT
}
/* Update constructor field `i` */
inline void cnstr_set(u_obj_arg o, unsigned i, obj_arg v) {
    lean_assert(!is_heap_obj(o) || !is_shared(o));
    lean_assert(i < cnstr_num_objs(o));
    obj_set_data(o, sizeof(constructor_object) + sizeof(object*)*i, v); // NOLINT
}
/* Release field `i`, that is, decrement its reference counter, and then set it to box(0) */
inline void cnstr_release(u_obj_arg o, unsigned i) {
    lean_assert(!is_heap_obj(o) || !is_shared(o));
    lean_assert(i < cnstr_num_objs(o));
    object ** field_ptr = reinterpret_cast<object **>(reinterpret_cast<char *>(o) + sizeof(constructor_object) + sizeof(object*)*i);
    dec(*field_ptr);
    *field_ptr = box(0);
}
/* Access scalar data at the given offset. */
template<typename T> inline T cnstr_get_scalar(b_obj_arg o, size_t offset) {
    return obj_data<T>(o, sizeof(constructor_object) + offset);
}
template<typename T> inline void cnstr_set_scalar(b_obj_arg o, unsigned i, T v) {
    obj_set_data(o, sizeof(constructor_object) + i, v);
}

inline unsigned obj_tag(b_obj_arg o) { if (is_scalar(o)) return unbox(o); else return cnstr_tag(o); }

// =======================================
// Closures

inline obj_res alloc_closure(void * fun, unsigned arity, unsigned num_fixed) {
    LEAN_RUNTIME_STAT_CODE(g_num_closure++);
    lean_assert(arity > 0);
    lean_assert(num_fixed < arity);
    return new (alloc_heap_object(closure_byte_size(num_fixed))) closure_object(fun, arity, num_fixed); // NOLINT
}
inline b_obj_res closure_get(b_obj_arg o, unsigned i) {
    lean_assert(i < closure_num_fixed(o));
    return obj_data<object*>(o, sizeof(closure_object) + sizeof(object*)*i); // NOLINT
}
inline void closure_set(u_obj_arg o, unsigned i, obj_arg a) {
    lean_assert(i < closure_num_fixed(o));
    obj_set_data(o, sizeof(closure_object) + sizeof(object*)*i, a); // NOLINT
}
inline obj_res alloc_closure(object*(*fun)(object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 1, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 2, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 3, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 4, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 5, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 6, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 7, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 8, num_fixed);
}

// =======================================
// Fixpoint

obj_res fixpoint(obj_arg rec, obj_arg a);
obj_res fixpoint2(obj_arg rec, obj_arg a1, obj_arg a2);
obj_res fixpoint3(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3);
obj_res fixpoint4(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4);
obj_res fixpoint5(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5);
obj_res fixpoint6(obj_arg rec, obj_arg a1, obj_arg a2, obj_arg a3, obj_arg a4, obj_arg a5, obj_arg a6);

// =======================================
// Array of objects

inline obj_res alloc_array(size_t size, size_t capacity) {
    LEAN_RUNTIME_STAT_CODE(g_num_array++);
    return new (alloc_heap_object(array_byte_size(capacity))) array_object(size, capacity); // NOLINT
}
inline size_t array_size(b_obj_arg o) { return to_array(o)->m_size; }
inline void array_set_size(u_obj_arg o, size_t sz) {
    lean_assert(is_array(o));
    lean_assert(!is_heap_obj(o) || !is_shared(o));
    lean_assert(sz <= array_capacity(o));
    to_array(o)->m_size = sz;
}
inline b_obj_res array_get(b_obj_arg o, size_t i) {
    lean_assert(i < array_size(o));
    return obj_data<object*>(o, sizeof(array_object) + sizeof(object*)*i); // NOLINT
}
inline void array_set(u_obj_arg o, size_t i, obj_arg v) {
    lean_assert(!is_heap_obj(o) || !is_shared(o));
    lean_assert(i < array_size(o));
    obj_set_data(o, sizeof(array_object) + sizeof(object*)*i, v); // NOLINT
}

// =======================================
// Persistent Array of objects

obj_res alloc_parray(size_t capacity);
size_t parray_size(b_obj_arg o);
b_obj_res parray_get(b_obj_arg o, size_t i);
obj_res parray_set(obj_arg o, size_t i, obj_arg v);
obj_res parray_push(obj_arg o, obj_arg v);
obj_res parray_pop(obj_arg o);
obj_res parray_copy(b_obj_arg o);

// =======================================

// =======================================
// Array of scalars

inline obj_res alloc_sarray(unsigned elem_size, size_t size, size_t capacity) {
    return new (alloc_heap_object(sarray_byte_size(capacity, elem_size))) sarray_object(elem_size, size, capacity); // NOLINT
}
inline size_t sarray_size(b_obj_arg o) { return to_sarray(o)->m_size; }
inline void sarray_set_size(u_obj_arg o, size_t sz) {
    lean_assert(is_sarray(o));
    lean_assert(!is_heap_obj(o) || !is_shared(o));
    lean_assert(sz <= sarray_capacity(o));
    to_sarray(o)->m_size = sz;
}
template<typename T> T sarray_get(b_obj_arg o, size_t i) { return sarray_cptr<T>(o)[i]; }
template<typename T> void sarray_set(u_obj_arg o, size_t i, T v) {
    obj_set_data(o, sizeof(sarray_object) + sizeof(T)*i, v);
}

// =======================================
// MPZ

inline mpz const & mpz_value(b_obj_arg o) { return to_mpz(o)->m_value; }

// =======================================
// Thunks

inline obj_res mk_thunk(obj_arg c) {
    LEAN_RUNTIME_STAT_CODE(g_num_thunk++);
    return new (alloc_heap_object(sizeof(thunk_object))) thunk_object(c, false); // NOLINT
}

/* thunk.pure : A -> thunk A */
inline obj_res thunk_pure(obj_arg v) {
    return new (alloc_heap_object(sizeof(thunk_object))) thunk_object(v, true); // NOLINT
}

/* Primitive for implementing the IR instruction for thunk.get : thunk A -> A */
inline b_obj_res thunk_get(b_obj_arg t) {
    if (object * r = to_thunk(t)->m_value)
        return r;
    return thunk_get_core(t);
}

obj_res thunk_map(obj_arg f, obj_arg t);
obj_res thunk_bind(obj_arg x, obj_arg f);

// =======================================
// Tasks

/* If num_workers == 0, then tasks primitives will just create thunks.
   It must not be used if task objects have already been created. */
class scoped_task_manager {
public:
    scoped_task_manager(unsigned num_workers);
    ~scoped_task_manager();
};

/* Convert a closure (unit -> A) into a task A */
obj_res mk_task(obj_arg c, unsigned prio = 0);
/* Convert a value `a : A` into `task A` */
obj_res task_pure(obj_arg a);
/* task.bind (x : task A) (f : A -> task B) : task B */
obj_res task_bind(obj_arg x, obj_arg f, unsigned prio = 0);
/* task.map (f : A -> B) (t : task A) : task B */
obj_res task_map(obj_arg f, obj_arg t, unsigned prio = 0);
/* task.get (t : task A) : A */
b_obj_res task_get(b_obj_arg t);

/* primitive for implementing `io.check_interrupt : io bool` */
bool io_check_interrupt_core();
/* primitive for implementing `io.request_interrupt : task A -> io unit` */
void io_request_interrupt_core(b_obj_arg t);
/* primitive for implementing `io.has_finished : task A -> io unit` */
bool io_has_finished_core(b_obj_arg t);
/* primitive for implementing `io.wait_any : list (task A) -> io (task A) */
b_obj_res io_wait_any_core(b_obj_arg task_list);

// =======================================
// Natural numbers

inline obj_res mk_nat_obj(mpz const & m) {
    if (m <= LEAN_MAX_SMALL_NAT)
        return box(m.get_unsigned_long_int());
    else
        return mk_nat_obj_core(m);
}

inline obj_res mk_nat_obj(usize n) {
    if (n <= LEAN_MAX_SMALL_NAT) {
        return box(n);
    } else {
        return mk_nat_obj_core(mpz(n));
    }
}

inline obj_res mk_nat_obj(unsigned n) {
    return mk_nat_obj(static_cast<usize>(n));
}

inline obj_res mk_nat_obj(uint64 n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT)) {
        return box(n);
    } else {
        return mk_nat_obj_core(mpz(n));
    }
}

inline uint64 nat2uint64(b_obj_arg a) {
    lean_assert(is_scalar(a));
    return unbox(a);
}

inline obj_res nat_succ(b_obj_arg a) {
    if (LEAN_LIKELY(is_scalar(a))) {
        return mk_nat_obj(nat2uint64(a) + 1);
    } else {
        return mk_nat_obj_core(mpz_value(a) + 1);
    }
}

inline obj_res nat_add(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        usize r  = unbox(a1) + unbox(a2);
        if (r <= LEAN_MAX_SMALL_NAT)
            return box(r);
        else
            return mk_nat_obj_core(mpz(r));
    } else {
        return nat_big_add(a1, a2);
    }
}

inline obj_res nat_sub(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        usize n1 = unbox(a1);
        usize n2 = unbox(a2);
        if (n1 < n2)
            return box(0);
        else
            return box(n1 - n2);
    } else {
        return nat_big_sub(a1, a2);
    }
}

inline obj_res nat_mul(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        usize n1 = unbox(a1);
        if (n1 == 0)
            return a1;
        usize n2 = unbox(a2);
        usize r  = n1*n2;
        if (r / n1 == n2)
            return box(r);
        else
            return mk_nat_obj_core(mpz(n1)*mpz(n2));
    } else {
        return nat_big_mul(a1, a2);
    }
}

inline obj_res nat_div(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        usize n1 = unbox(a1);
        usize n2 = unbox(a2);
        if (n2 == 0)
            return box(0);
        else
            return box(n1 / n2);
    } else {
        return nat_big_div(a1, a2);
    }
}

inline obj_res nat_mod(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        usize n1 = unbox(a1);
        usize n2 = unbox(a2);
        if (n2 == 0)
            return box(0);
        else
            return box(n1 % n2);
    } else {
        return nat_big_mod(a1, a2);
    }
}

inline bool nat_eq(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 == a2;
    } else {
        return nat_big_eq(a1, a2);
    }
}

inline uint8 nat_dec_eq(b_obj_arg a1, b_obj_arg a2) { return nat_eq(a1, a2); }

inline bool nat_ne(b_obj_arg a1, b_obj_arg a2) {
    return !nat_eq(a1, a2);
}

inline bool nat_le(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 <= a2;
    } else {
        return nat_big_le(a1, a2);
    }
}

inline uint8 nat_dec_le(b_obj_arg a1, b_obj_arg a2) { return nat_le(a1, a2); }

inline bool nat_lt(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 < a2;
    } else {
        return nat_big_lt(a1, a2);
    }
}

inline uint8 nat_dec_lt(b_obj_arg a1, b_obj_arg a2) { return nat_lt(a1, a2); }

inline obj_res nat_land(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return reinterpret_cast<object*>(reinterpret_cast<usize>(a1) & reinterpret_cast<usize>(a2));
    } else {
        return nat_big_land(a1, a2);
    }
}

inline obj_res nat_lor(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return reinterpret_cast<object*>(reinterpret_cast<usize>(a1) | reinterpret_cast<usize>(a2));
    } else {
        return nat_big_lor(a1, a2);
    }
}

inline obj_res nat_lxor(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return box(unbox(a1) ^ unbox(a2));
    } else {
        return nat_big_xor(a1, a2);
    }
}

// =======================================
// Integers

inline obj_res mk_int_obj(mpz const & m) {
    if (m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT)
        return mk_int_obj_core(m);
    else
        return box(static_cast<unsigned>(m.get_int()));
}

inline obj_res mk_int_obj(int n) {
    if (sizeof(void*) == 8) { // NOLINT
        return box(static_cast<unsigned>(n));
    } else if (LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT) {
        return box(static_cast<unsigned>(n));
    } else {
        return alloc_mpz(mpz(n));
    }
}

inline obj_res mk_int_obj(int64 n) {
    if (LEAN_LIKELY(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT)) {
        return box(static_cast<unsigned>(static_cast<int>(n)));
    } else {
        return mk_int_obj_core(mpz(n));
    }
}

inline int64 int2int64(b_obj_arg a) {
    lean_assert(is_scalar(a));
    if (sizeof(void*) == 8) { // NOLINT
        return static_cast<int>(static_cast<unsigned>(unbox(a)));
    } else {
        return static_cast<int>(reinterpret_cast<size_t>(a)) >> 1;
    }
}

inline int int2int(b_obj_arg a) {
    lean_assert(is_scalar(a));
    if (sizeof(void*) == 8) { // NOLINT
        return static_cast<int>(static_cast<unsigned>(unbox(a)));
    } else {
        return static_cast<int>(reinterpret_cast<size_t>(a)) >> 1;
    }
}

inline obj_res nat2int(obj_arg a) {
    if (is_scalar(a)) {
        usize v = unbox(a);
        if (v <= LEAN_MAX_SMALL_INT) {
            return a;
        } else {
            return alloc_mpz(mpz(v));
        }
    } else {
        return a;
    }
}

inline obj_res int_neg(b_obj_arg a) {
    if (LEAN_LIKELY(is_scalar(a))) {
        return mk_int_obj(-int2int64(a));
    } else {
        return mk_int_obj(neg(mpz_value(a)));
    }
}

inline obj_res int_neg_succ_of_nat(obj_arg a) {
    obj_res s  = nat_succ(a);
    obj_res i  = nat2int(s);
    obj_res r  = int_neg(i);
    dec(s); dec(i); dec(a);
    return r;
}

inline obj_res int_add(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_int_obj(int2int64(a1) + int2int64(a2));
    } else {
        return int_big_add(a1, a2);
    }
}

inline obj_res int_sub(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_int_obj(int2int64(a1) - int2int64(a2));
    } else {
        return int_big_sub(a1, a2);
    }
}

inline obj_res int_mul(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_int_obj(int2int64(a1) * int2int64(a2));
    } else {
        return int_big_mul(a1, a2);
    }
}

inline obj_res int_div(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        int v1 = int2int(a1);
        int v2 = int2int(a2);
        if (v2 == 0)
            return box(0);
        else
            return mk_int_obj(v1 / v2);
    } else {
        return int_big_div(a1, a2);
    }
}

inline obj_res int_mod(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        int v1 = int2int(a1);
        int v2 = int2int(a2);
        if (v2 == 0)
            return box(0);
        else
            return mk_int_obj(v1 % v2);
    } else {
        return int_big_mod(a1, a2);
    }
}

inline bool int_eq(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 == a2;
    } else {
        return int_big_eq(a1, a2);
    }
}

inline bool int_ne(b_obj_arg a1, b_obj_arg a2) {
    return !int_eq(a1, a2);
}

inline bool int_le(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return int2int(a1) <= int2int(a2);
    } else {
        return int_big_le(a1, a2);
    }
}

inline bool int_lt(b_obj_arg a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return int2int(a1) < int2int(a2);
    } else {
        return int_big_lt(a1, a2);
    }
}

inline obj_res nat_abs(b_obj_arg i) {
    if (int_lt(i, mk_int_obj(0))) {
        return int_neg(i);
    } else {
        inc(i);
        return i;
    }
}

inline uint8 int_dec_eq(b_obj_arg a1, b_obj_arg a2) { return int_eq(a1, a2); }

inline uint8 int_dec_le(b_obj_arg a1, b_obj_arg a2) { return int_le(a1, a2); }

inline uint8 int_dec_lt(b_obj_arg a1, b_obj_arg a2) { return int_lt(a1, a2); }

inline uint8 int_dec_nonneg(b_obj_arg a) {
    if (LEAN_LIKELY(is_scalar(a))) {
        return int2int(a) >= 0;
    } else {
        return mpz_value(a) >= 0;
    }
}

inline obj_res box_uint32(unsigned v) {
    if (sizeof(void*) == 4) {
        // 32-bit implementation
        obj_res r = alloc_cnstr(0, 0, sizeof(unsigned));
        cnstr_set_scalar(r, 0, v);
        return r;
    } else {
        // 64-bit implementation
        return box(v);
    }
}

inline unsigned unbox_uint32(b_obj_arg o) {
    if (sizeof(void*) == 4) {
        // 32-bit implementation
        return cnstr_get_scalar<unsigned>(o, 0);
    } else {
        // 64-bit implementation
        return unbox(o);
    }
}

inline obj_res box_uint64(unsigned long long v) {
    obj_res r = alloc_cnstr(0, 0, sizeof(unsigned long long));
    cnstr_set_scalar(r, 0, v);
    return r;
}

inline unsigned long long unbox_uint64(b_obj_arg o) {
    return cnstr_get_scalar<unsigned long long>(o, 0);
}

inline obj_res box_size_t(size_t v) {
    obj_res r = alloc_cnstr(0, 0, sizeof(size_t));
    cnstr_set_scalar(r, 0, v);
    return r;
}

inline size_t unbox_size_t(b_obj_arg o) {
    return cnstr_get_scalar<size_t>(o, 0);
}

// =======================================
// Option

inline obj_res mk_option_none() { return box(0); }
inline obj_res mk_option_some(obj_arg v) { obj_res r = alloc_cnstr(1, 1, 0); cnstr_set(r, 0, v); return r; }

// =======================================
// String

/* instance : inhabited char := ⟨'A'⟩ */
inline uint32 char_default_value() { return 'A'; }
inline obj_res alloc_string(size_t size, size_t capacity, size_t len) {
    LEAN_RUNTIME_STAT_CODE(g_num_string++);
    return new (alloc_heap_object(string_byte_size(capacity))) string_object(size, capacity, len); // NOLINT
}
obj_res mk_string(char const * s);
obj_res mk_string(std::string const & s);
std::string string_to_std(b_obj_arg o);
inline char const * string_cstr(b_obj_arg o) { lean_assert(is_string(o)); return reinterpret_cast<char*>(o) + sizeof(string_object); }
inline size_t string_size(b_obj_arg o) { return to_string(o)->m_size; }
inline size_t string_len(b_obj_arg o) { return to_string(o)->m_length; }
obj_res string_push(obj_arg s, uint32 c);
obj_res string_append(obj_arg s1, b_obj_arg s2);
inline obj_res string_length(b_obj_arg s) { return mk_nat_obj(string_len(s)); } // TODO(Leo): improve
obj_res string_mk(obj_arg cs);
obj_res string_data(obj_arg s);

uint32 string_utf8_get_old(b_obj_arg s, usize i);
usize string_utf8_next_old(b_obj_arg s, usize i);
usize string_utf8_prev_old(b_obj_arg s, usize i);
obj_res string_utf8_set_old(obj_arg s, usize i, uint32 c);
inline uint8 string_utf8_at_end_old(b_obj_arg s, usize i) { return i >= string_size(s) - 1; }
obj_res string_utf8_extract_old(b_obj_arg s, usize b, usize e);
inline usize string_utf8_byte_size_old(b_obj_arg s) { return string_size(s) - 1; }

inline uint32 string_utf8_get(b_obj_arg s, usize i) { return string_utf8_get_old(s, i); }
inline usize string_utf8_next(b_obj_arg s, usize i) { return string_utf8_next_old(s, i); }
inline usize string_utf8_prev(b_obj_arg s, usize i) { return string_utf8_prev_old(s, i); }
inline obj_res string_utf8_set(obj_arg s, usize i, uint32 c) { return string_utf8_set_old(s, i, c); }
inline uint8 string_utf8_at_end(b_obj_arg s, usize i) { return string_utf8_at_end_old(s, i); }
inline obj_res string_utf8_extract(b_obj_arg s, usize b, usize e) { return string_utf8_extract_old(s, b, e); }
inline usize string_utf8_byte_size(b_obj_arg s) { return string_size(s) - 1; }

inline bool string_eq(b_obj_arg s1, b_obj_arg s2) { return s1 == s2 || (string_size(s1) == string_size(s2) && std::memcmp(string_cstr(s1), string_cstr(s2), string_size(s1)) == 0); }
bool string_eq(b_obj_arg s1, char const * s2);
inline bool string_ne(b_obj_arg s1, b_obj_arg s2) { return !string_eq(s1, s2); }
bool string_lt(b_obj_arg s1, b_obj_arg s2);
inline uint8 string_dec_eq(b_obj_arg s1, b_obj_arg s2) { return string_eq(s1, s2); }
inline uint8 string_dec_lt(b_obj_arg s1, b_obj_arg s2) { return string_lt(s1, s2); }

// =======================================
// uint8
inline uint8 uint8_of_nat(b_obj_arg a) { return is_scalar(a) ? static_cast<uint8>(unbox(a)) : 0; }
inline obj_res uint8_to_nat(uint8 a) { return mk_nat_obj(static_cast<usize>(a)); }
inline uint8 uint8_add(uint8 a1, uint8 a2) { return a1+a2; }
inline uint8 uint8_sub(uint8 a1, uint8 a2) { return a1-a2; }
inline uint8 uint8_mul(uint8 a1, uint8 a2) { return a1*a2; }
inline uint8 uint8_div(uint8 a1, uint8 a2) { return a2 == 0 ? 0 : a1/a2; }
inline uint8 uint8_mod(uint8 a1, uint8 a2) { return a2 == 0 ? 0 : a1%a2; }
inline uint8 uint8_modn(uint8 a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a2))) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? 0 : a1 % n2;
    } else {
        return a1;
    }
}
inline uint8 uint8_dec_eq(uint8 a1, uint8 a2) { return a1 == a2; }
inline uint8 uint8_dec_lt(uint8 a1, uint8 a2) { return a1 < a2; }
inline uint8 uint8_dec_le(uint8 a1, uint8 a2) { return a1 <= a2; }

// =======================================
// uint16
inline uint16 uint16_of_nat(b_obj_arg a) { return is_scalar(a) ? static_cast<uint16>(unbox(a)) : 0; }
inline obj_res uint16_to_nat(uint16 a) { return mk_nat_obj(static_cast<usize>(a)); }
inline uint16 uint16_add(uint16 a1, uint16 a2) { return a1+a2; }
inline uint16 uint16_sub(uint16 a1, uint16 a2) { return a1-a2; }
inline uint16 uint16_mul(uint16 a1, uint16 a2) { return a1*a2; }
inline uint16 uint16_div(uint16 a1, uint16 a2) { return a2 == 0 ? 0 : a1/a2; }
inline uint16 uint16_mod(uint16 a1, uint16 a2) { return a2 == 0 ? 0 : a1%a2; }
inline uint16 uint16_modn(uint16 a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a2))) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? 0 : a1 % n2;
    } else {
        return a1;
    }
}
inline uint8 uint16_dec_eq(uint16 a1, uint16 a2) { return a1 == a2; }
inline uint8 uint16_dec_lt(uint16 a1, uint16 a2) { return a1 < a2; }
inline uint8 uint16_dec_le(uint16 a1, uint16 a2) { return a1 <= a2; }

// =======================================
// uint32
inline uint32 uint32_of_nat(b_obj_arg a) {
    if (is_scalar(a)) {
        usize v = unbox(a);
        if (v < std::numeric_limits<uint32>::max())
            return v;
        else
            return 0;
    } else if (sizeof(void*) == 4) {
        // 32-bit
        mpz const & m = mpz_value(a);
        return m.is_unsigned_int() ? mpz_value(a).get_unsigned_int() : 0;
    } else {
        // 64-bit
        return 0;
    }
}
inline obj_res uint32_to_nat(uint32 a) { return mk_nat_obj(static_cast<usize>(a)); }
inline uint32 uint32_add(uint32 a1, uint32 a2) { return a1+a2; }
inline uint32 uint32_sub(uint32 a1, uint32 a2) { return a1-a2; }
inline uint32 uint32_mul(uint32 a1, uint32 a2) { return a1*a2; }
inline uint32 uint32_div(uint32 a1, uint32 a2) { return a2 == 0 ? 0 : a1/a2; }
inline uint32 uint32_mod(uint32 a1, uint32 a2) { return a2 == 0 ? 0 : a1%a2; }
inline uint32 uint32_modn(uint32 a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a2))) {
        usize n2 = unbox(a2);
        return n2 == 0 ? 0 : a1 % n2;
    } else if (sizeof(void*) == 4) {
        // 32-bit
        mpz const & m = mpz_value(a2);
        return m.is_unsigned_int() ? a1 % m.get_unsigned_int() : a1;
    } else {
        // 64-bit
        return a1;
    }
}
inline uint8 uint32_dec_eq(uint32 a1, uint32 a2) { return a1 == a2; }
inline uint8 uint32_dec_lt(uint32 a1, uint32 a2) { return a1 < a2; }
inline uint8 uint32_dec_le(uint32 a1, uint32 a2) { return a1 <= a2; }

// =======================================
// uint64
inline uint64 uint64_of_nat(b_obj_arg a) {
    if (is_scalar(a)) {
        return unbox(a);
    } else {
        // TODO(Leo):
        return 0;
    }
}
inline obj_res uint64_to_nat(uint64 a) { return mk_nat_obj(a); }
inline uint64 uint64_add(uint64 a1, uint64 a2) { return a1+a2; }
inline uint64 uint64_sub(uint64 a1, uint64 a2) { return a1-a2; }
inline uint64 uint64_mul(uint64 a1, uint64 a2) { return a1*a2; }
inline uint64 uint64_div(uint64 a1, uint64 a2) { return a2 == 0 ? 0 : a1/a2; }
inline uint64 uint64_mod(uint64 a1, uint64 a2) { return a2 == 0 ? 0 : a1%a2; }
inline uint64 uint64_modn(uint64 a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a2))) {
        usize n2 = unbox(a2);
        return n2 == 0 ? 0 : a1 % n2;
    } else {
        // TODO(Leo)
        return a1;
    }
}
inline uint8 uint64_dec_eq(uint64 a1, uint64 a2) { return a1 == a2; }
inline uint8 uint64_dec_lt(uint64 a1, uint64 a2) { return a1 < a2; }
inline uint8 uint64_dec_le(uint64 a1, uint64 a2) { return a1 <= a2; }

// =======================================
// usize
inline usize usize_of_nat(b_obj_arg a) {
    if (is_scalar(a)) {
        return unbox(a);
    } else {
        // TODO(Leo):
        return 0;
    }
}
inline obj_res usize_to_nat(usize a) {
    return mk_nat_obj(a);
}
inline usize usize_add(usize a1, usize a2) { return a1+a2; }
inline usize usize_sub(usize a1, usize a2) { return a1-a2; }
inline usize usize_mul(usize a1, usize a2) { return a1*a2; }
inline usize usize_div(usize a1, usize a2) { return a2 == 0 ? 0 : a1/a2; }
inline usize usize_mod(usize a1, usize a2) { return a2 == 0 ? 0 : a1%a2; }
inline usize usize_modn(usize a1, b_obj_arg a2) {
    if (LEAN_LIKELY(is_scalar(a2))) {
        usize n2 = unbox(a2);
        return n2 == 0 ? 0 : a1 % n2;
    } else {
        // TODO(Leo)
        return a1;
    }
}
inline uint8 usize_dec_eq(usize a1, usize a2) { return a1 == a2; }
inline uint8 usize_dec_lt(usize a1, usize a2) { return a1 < a2; }
inline uint8 usize_dec_le(usize a1, usize a2) { return a1 <= a2; }

// =======================================
// array functions for generated code
static_assert(sizeof(unsigned long) == sizeof(size_t), "we assume that `unsigned long` and `size_t` have the same size");

inline object * array_sz(obj_arg a) {
    object * r = box(array_size(a));
    dec(a);
    return r;
}

inline object * array_get_size(b_obj_arg a) {
    return box(array_size(a));
}

object * mk_array(obj_arg n, obj_arg v);

inline object * mk_empty_array() {
    return alloc_array(0, 0);
}

inline object * array_idx(b_obj_arg a, usize i) {
    object * r = array_get(a, i); inc(r);
    return r;
}

inline obj_res array_index(b_obj_arg a, b_obj_arg i) {
    return array_idx(a, unbox(i));
}

inline object * array_get(obj_arg def_val, b_obj_arg a, b_obj_arg i) {
    if (is_scalar(i)) {
        usize idx = unbox(i);
        if (idx < array_size(a)) {
            dec(def_val);
            return array_idx(a, idx);
        } else {
            return def_val;
        }
    } else {
        /* The index must be out of bounds because
           i > LEAN_MAX_SMALL_NAT == std::numeric_limits<unsigned>::max() >> 1,
           but each array entry is 8 bytes in 64-bit machines and 4 in 32-bit ones.
           In both cases, we would be out-of-memory. */
        return def_val;
    }
}

obj_res copy_array(obj_arg a, bool expand = false);

inline obj_res ensure_exclusive_array(obj_arg a) {
    if (is_exclusive(a)) return a;
    return copy_array(a);
}

inline object * array_updt(obj_arg a, usize i, obj_arg v) {
    object * r   = ensure_exclusive_array(a);
    object ** it = array_cptr(r) + i;
    dec(*it);
    *it = v;
    return r;
}

inline object * array_update(obj_arg a, b_obj_arg i, obj_arg v) {
    return array_updt(a, unbox(i), v);
}

inline object * array_safe_uwrite(obj_arg a, usize i, obj_arg v) {
    if (i < array_size(a)) {
        return array_updt(a, i, v);
    } else {
        dec(v);
        return a;
    }
}

inline object * array_set(obj_arg a, b_obj_arg i, obj_arg v) {
    if (is_scalar(i)) {
        usize idx = unbox(i);
        if (idx < array_size(a))
            return array_updt(a, idx, v);
    }
    dec(v);
    return a;
}

inline object * array_pop(obj_arg a) {
    object * r  = ensure_exclusive_array(a);
    size_t & sz = to_array(r)->m_size;
    if (sz == 0) return r;
    sz--;
    object ** last = array_cptr(r) + sz;
    dec(*last);
    return r;
}

object * array_push(obj_arg a, obj_arg v);

// =======================================
// debugging helper functions
object * dbg_trace(obj_arg s, obj_arg fn);
object * dbg_sleep(uint32 ms, obj_arg fn);

// =======================================
// IO helper functions
inline obj_res io_mk_world() {
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, box(0));
    cnstr_set(r, 1, box(0));
    return r;
}
inline bool io_result_is_ok(b_obj_arg r) { return cnstr_tag(r) == 0; }
inline bool io_result_is_error(b_obj_arg r) { return cnstr_tag(r) == 1; }
inline b_obj_res io_result_get_value(b_obj_arg r) { lean_assert(io_result_is_ok(r)); return cnstr_get(r, 0); }
inline b_obj_arg io_result_get_error(b_obj_arg r) { lean_assert(io_result_is_error(r)); return cnstr_get(r, 0); }
void io_result_show_error(b_obj_arg r);

// =======================================
// IO ref primitives
obj_res io_mk_ref(obj_arg, obj_arg);
obj_res io_ref_get(b_obj_arg, obj_arg);
obj_res io_ref_set(b_obj_arg, obj_arg, obj_arg);
obj_res io_ref_reset(b_obj_arg, obj_arg);
obj_res io_ref_swap(b_obj_arg, obj_arg, obj_arg);

// =======================================
// Module initialization/finalization
void initialize_object();
void finalize_object();
}
