/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/thread.h"
#include "util/debug.h"
#include "util/mpz.h"

namespace lean {

enum class lean_obj_kind {
    Constructor, BigConstructor,
    Closure, Array, ScalarArray,
    String, MPZ, External };

struct lean_obj {
    atomic<unsigned> m_rc;
    unsigned         m_kind:8;
    lean_obj(lean_obj_kind k):m_rc(0), m_kind(static_cast<unsigned>(k)) {}
};

/* We can use regular constructor objects to represent inductive datatypes that
   have:
   1) At most 256 constructors
   2) At most 256 object fields per constructor
   3) At most 256*4 bytes for scalar/unboxed fields

   We only need m_scalar_size for implementing sanity checks at runtime.

   Header size: 8 bytes in 32 and 64 bit machines. */
struct lean_constructor : public lean_obj {
    unsigned    m_tag:8;
    unsigned    m_num_objs:8;
    unsigned    m_scalar_size:8;

    lean_constructor(unsigned tag, unsigned num_objs, unsigned scalar_sz):
        lean_obj(lean_obj_kind::Constructor), m_tag(tag), m_num_objs(num_objs), m_scalar_size(scalar_sz) {}
};

/* Similar to lean_constructor, but without the restriction on the field sizes.

   Remark: for the vast majority of inductive datatypes defined in Lean, we are assuming
   we can represent their values using `lean_constructor` instead of `lean_big_constructor`.

   Header size: 20 bytes in 32 bit machines, and 24 bytes in 64 bit machines. */
struct lean_big_constructor : public lean_obj {
    unsigned m_tag;
    unsigned m_num_objs;
    unsigned m_scalar_size;

    lean_big_constructor(unsigned tag, unsigned num_objs, unsigned scalar_sz):
        lean_obj(lean_obj_kind::BigConstructor), m_tag(tag), m_num_objs(num_objs), m_scalar_size(scalar_sz) {}
};

/* Array of objects.

   Remark: we are assuming that this kind of array has at most 2^32 objects.
   So, the array would consume 32Gb without counting the objects stored on it.

   Header size: 16 bytes in 32 and 64 bit machines. */
struct lean_array : public lean_obj {
    unsigned m_size;
    unsigned m_capacity;
    lean_array(unsigned sz, unsigned c):
        lean_obj(lean_obj_kind::Array), m_size(sz), m_capacity(c) {}
};

/* Array of scalar values.
   We support arrays with upto 2^64 elements in 64 bit machines.

   The field m_elem_size is only needed for implementing sanity checks at runtime.
   Header size: 24 bytes in 32 and 64 bit machines. */
struct lean_scalar_array : public lean_obj {
    unsigned m_elem_size:8;
    size_t   m_size;
    size_t   m_capacity;
    lean_scalar_array(unsigned esz, unsigned sz, unsigned c):
        lean_obj(lean_obj_kind::ScalarArray), m_elem_size(esz), m_size(sz), m_capacity(c) {}
};

typedef lean_obj * (*lean_cfun)(lean_obj *);

/* Note that `lean_cfun` is a function pointer for a C function of
   arity 1. The `apply` operator performs a cast operation.
   It casts m_fun to a C function of the right arity.

   Header size: 20 bytes in 32 bit machines, 24 bytes in 64 bit machines.

   Remark: we can reduce the header size to 16 bytes in 64 bit machines if
   we assume function can have at most 255 arguments.
   We can even support at most 2^12 arguments if we sacrifice performance and
   use 12-bits for m_arity and m_num_args.

   Note that this structure may also be used to simulate closures built
   from bytecodes. We just store an extra argument: the virtual machine
   function descriptor. We store in m_fun a pointer to a C function
   that extracts the function descriptor and then invokes the VM. */
struct lean_closure : public lean_obj {
    unsigned  m_arity;     /* number of arguments expected by m_fun. */
    unsigned  m_num_fixed; /* number of arguments that have been already fixed. */
    lean_cfun m_fun;
    lean_closure(lean_cfun f, unsigned arity, unsigned n):
        lean_obj(lean_obj_kind::Closure), m_arity(arity), m_num_fixed(n), m_fun(f) {}
};

/* Header size: 20 bytes in 32 bit machines, 32 bytes in 64 bit machines.

   Remark: in Lean3, we have used std::string, but this adds an extra
   level of indirection. Moreover, most compilers use a reference counter
   in the implementation. */
struct lean_string : public lean_obj {
    size_t      m_size;     // in bytes
    size_t      m_capacity; // in bytes
    size_t      m_length;   // number of unicode scalar values
};

struct lean_mpz : public lean_obj {
    mpz m_value;
};

/* Base class for wrapping external data.
   For example, we use it to wrap the Lean environment object.

   Header size: 12 bytes in 32 bit machines, 16 bytes in 64 bit machines. */
struct lean_external : public lean_obj {
    virtual void dealloc() {}
    virtual ~lean_external() {}
};

inline bool is_scalar(lean_obj * o) { return (reinterpret_cast<uintptr_t>(o) & 1) == 1; }
inline lean_obj * box(unsigned n) { return reinterpret_cast<lean_obj*>(static_cast<uintptr_t>((n << 1) | 1)); }
inline unsigned unbox(lean_obj * o) { return reinterpret_cast<uintptr_t>(o) >> 1; }

/* Generic Lean object deallocator.

   The generic deallocator must be used when we are compiling:
   1- Polymorphic code.
   2- Code using `any` type.
      The `any` type is introduced when we translate Lean expression into the Core language based on System-F.

   We are planning to generate deallocators for non-polymorphic code.
   They can be faster because:
   1- They do not need to test whether nested pointers are boxed scalars or not.
   2- They do not need to test the kind.
   3- They can unfold the loop that decrements the reference counters for nested objects.

   \pre !is_scalar(o); */
void dealloc(lean_obj * o);

inline unsigned get_rc(lean_obj * o) { return atomic_load_explicit(&(o->m_rc), memory_order_acquire); }
inline bool is_shared(lean_obj * o) { return get_rc(o) > 1; }
inline void inc_ref(lean_obj * o) { atomic_fetch_add_explicit(&o->m_rc, 1u, memory_order_relaxed); }
inline void dec_shared_ref(lean_obj * o) { lean_assert(is_shared(o)); atomic_fetch_sub_explicit(&o->m_rc, 1u, memory_order_acq_rel); }
inline bool dec_ref_core(lean_obj * o) { lean_assert(get_rc(o) > 0); return atomic_fetch_sub_explicit(&o->m_rc, 1u, memory_order_acq_rel) == 1; }
inline void dec_ref(lean_obj * o) { if (dec_ref_core(o)) dealloc(o); }

/* Low-level operations for allocating lean objects.

   They do not initialize nested objects and scalar values. */
inline lean_obj * alloc_constructor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    return new (malloc(sizeof(lean_constructor) + num_objs * sizeof(lean_obj *) + scalar_sz * 4)) lean_constructor(tag, num_objs, scalar_sz);
}

inline lean_obj * alloc_big_constructor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    return new (malloc(sizeof(lean_big_constructor) + num_objs * sizeof(lean_obj *) + scalar_sz * 4)) lean_big_constructor(tag, num_objs, scalar_sz);
}
}
