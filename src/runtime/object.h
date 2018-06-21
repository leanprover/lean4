/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <cstdlib>
#if !defined(__APPLE__)
#include <malloc.h>
#endif
#include "runtime/compiler_hints.h"
#include "runtime/mpz.h"
#include "runtime/int64.h"
#include "runtime/thread.h"

namespace lean {
inline void * alloca(size_t s) {
#ifdef _MSC_VER
    return ::_alloca(s);
#else
    return ::alloca(s);
#endif
}

enum class object_kind { Constructor, Closure, Array, ScalarArray, String, MPZ, External };

/* The reference counter is a uintptr_t, because at deletion time, we use this field to implement
   a linked list of objects to be deleted. */
typedef uintptr_t rc_type;

struct object {
    atomic<rc_type> m_rc;
    unsigned        m_kind:16;
    object(object_kind k):m_rc(1), m_kind(static_cast<unsigned>(k)) {}
};

/* We can represent inductive datatypes that have:
   1) At most 2^16 constructors
   2) At most 2^16 - 1 object fields per constructor
   3) At most 2^16 - 1 bytes for scalar/unboxed fields

   We only need m_scalar_size for implementing sanity checks at runtime.

   Header size: 12 bytes in 32 bit machines and 16 bytes in 64 bit machines. */
struct constructor_object : public object {
    unsigned    m_tag:16;
    unsigned    m_num_objs:16;
    unsigned    m_scalar_size:16;
    constructor_object(unsigned tag, unsigned num_objs, unsigned scalar_sz):
        object(object_kind::Constructor), m_tag(tag), m_num_objs(num_objs), m_scalar_size(scalar_sz) {}
};

/* Array of objects.
   Header size: 16 bytes in 32 bit machines and 32 bytes in 64 bit machines. */
struct array_object : public object {
    size_t   m_size;
    size_t   m_capacity;
    array_object(size_t sz, size_t c):
        object(object_kind::Array), m_size(sz), m_capacity(c) {}
};

/* Array of scalar values.
   We support arrays with upto 2^64 elements in 64 bit machines.

   The field m_elem_size is only needed for implementing sanity checks at runtime.
   Header size: 16 bytes in 32 bit machines and 32 bytes in 64 bit machines. */
struct sarray_object : public object {
    unsigned m_elem_size:16; // in bytes
    size_t   m_size;
    size_t   m_capacity;
    sarray_object(unsigned esz, size_t sz, size_t c):
        object(object_kind::ScalarArray), m_elem_size(esz), m_size(sz), m_capacity(c) {}
};

struct string_object : public object {
    size_t m_size;
    size_t m_capacity;
    size_t m_length;   // UTF8 length
    string_object(size_t sz, size_t c, size_t len):
        object(object_kind::String), m_size(sz), m_capacity(c), m_length(len) {}
};

typedef object * (*lean_cfun)(object *); // NOLINT

/* Note that `lean_cfun` is a function pointer for a C function of
   arity 1. The `apply` operator performs a cast operation.
   It casts m_fun to a C function of the right arity.

   Header size: 16 bytes in 32 bit machines and 24 bytes in 64 bit machines.

   Note that this structure may also be used to simulate closures built
   from bytecodes. We just store an extra argument: the virtual machine
   function descriptor. We store in m_fun a pointer to a C function
   that extracts the function descriptor and then invokes the VM. */
struct closure_object : public object {
    unsigned  m_arity:16;     // number of arguments expected by m_fun.
    unsigned  m_num_fixed:16; // number of arguments that have been already fixed.
    lean_cfun m_fun;
    closure_object(lean_cfun f, unsigned arity, unsigned n):
        object(object_kind::Closure), m_arity(arity), m_num_fixed(n), m_fun(f) {}
};

struct mpz_object : public object {
    mpz m_value;
    mpz_object(mpz const & v):
        object(object_kind::MPZ), m_value(v) {}
};

/* Base class for wrapping external_object data.
   For example, we use it to wrap the Lean environment object. */
struct external_object : public object {
    virtual void dealloc() {}
    virtual ~external_object() {}
};

inline bool is_null(object * o) { return o == nullptr; }
inline bool is_scalar(object * o) { return (reinterpret_cast<uintptr_t>(o) & 1) == 1; }
inline object * box(unsigned n) { return reinterpret_cast<object*>((static_cast<uintptr_t>(n) << 1) | 1); }
inline unsigned unbox(object * o) { return reinterpret_cast<uintptr_t>(o) >> 1; }

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

inline unsigned get_rc(object * o) { lean_assert(!is_scalar(o)); return atomic_load_explicit(&(o->m_rc), memory_order_acquire); }
inline bool is_shared(object * o) { return get_rc(o) > 1; }
inline void inc_ref(object * o) { atomic_fetch_add_explicit(&o->m_rc, static_cast<rc_type>(1), memory_order_relaxed); }
inline void dec_shared_ref(object * o) { lean_assert(is_shared(o)); atomic_fetch_sub_explicit(&o->m_rc, static_cast<rc_type>(1), memory_order_acq_rel); }
inline bool dec_ref_core(object * o) { lean_assert(get_rc(o) > 0); return atomic_fetch_sub_explicit(&o->m_rc, static_cast<rc_type>(1), memory_order_acq_rel) == 1; }
inline void dec_ref(object * o) { if (dec_ref_core(o)) del(o); }
inline void inc(object * o) { if (!is_scalar(o)) inc_ref(o); }
inline void dec(object * o) { if (!is_scalar(o)) dec_ref(o); }

/* Testers */
inline object_kind get_kind(object * o) { return static_cast<object_kind>(o->m_kind); }
inline bool is_cnstr(object * o) { return get_kind(o) == object_kind::Constructor; }
inline bool is_closure(object * o) { return get_kind(o) == object_kind::Closure; }
inline bool is_array(object * o) { return get_kind(o) == object_kind::Array; }
inline bool is_sarray(object * o) { return get_kind(o) == object_kind::ScalarArray; }
inline bool is_string(object * o) { return get_kind(o) == object_kind::String; }
inline bool is_mpz(object * o) { return get_kind(o) == object_kind::MPZ; }
inline bool is_external(object * o) { return get_kind(o) == object_kind::External; }

/* Casting */
inline constructor_object * to_cnstr(object * o) { lean_assert(is_cnstr(o)); return static_cast<constructor_object*>(o); }
inline closure_object * to_closure(object * o) { lean_assert(is_closure(o)); return static_cast<closure_object*>(o); }
inline array_object * to_array(object * o) { lean_assert(is_array(o)); return static_cast<array_object*>(o); }
inline sarray_object * to_sarray(object * o) { lean_assert(is_sarray(o)); return static_cast<sarray_object*>(o); }
inline string_object * to_string(object * o) { lean_assert(is_string(o)); return static_cast<string_object*>(o); }
inline mpz_object * to_mpz(object * o) { lean_assert(is_mpz(o)); return static_cast<mpz_object*>(o); }
inline external_object * to_external(object * o) { lean_assert(is_external(o)); return static_cast<external_object*>(o); }

/* The memory associated with all Lean objects but `mpz_object` and `external_object` can be deallocated using `free`.
   All fields in these objects are integral types, but `std::atomic<uintptr_t> m_rc`.
   However, `std::atomic<Integral>` has a trivial destructor.
   In the C++ reference manual (http://en.cppreference.com/w/cpp/atomic/atomic), we find the following sentence:

   "Additionally, the resulting std::atomic<Integral> specialization has standard layout, a trivial default constructor,
   and a trivial destructor." */
inline void dealloc_mpz(object * o) { delete to_mpz(o); }
inline void dealloc_external(object * o) { delete to_external(o); }
inline void dealloc(object * o) {
    switch (get_kind(o)) {
    case object_kind::External: dealloc_external(o); break;
    case object_kind::MPZ: dealloc_mpz(o); break;
    default: free(o); break;
    }
}

/* Size of the object in bytes. This function is used for debugging purposes.
   \pre !is_scalar(o) && !is_external(o) */
size_t obj_byte_size(object * o);

/* Size of the object header in bytes. This function is used for debugging purposes.
   \pre !is_scalar(o) && !is_external(o) */
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
    lean_assert(!is_shared(o));
    lean_assert(obj_header_size(o) <= offset);
    lean_assert(offset + sizeof(T) <= obj_byte_size(o));
    *(reinterpret_cast<T *>(reinterpret_cast<char *>(o) + offset)) = v;
}

/* Constructor objects */
inline object * alloc_cnstr(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    lean_assert(tag < 65536 && num_objs < 65536 && scalar_sz < 65536);
    return new (malloc(sizeof(constructor_object) + num_objs * sizeof(object *) + scalar_sz)) constructor_object(tag, num_objs, scalar_sz); // NOLINT
}
inline unsigned cnstr_tag(object * o) { return to_cnstr(o)->m_tag; }
inline unsigned cnstr_num_objs(object * o) { return to_cnstr(o)->m_num_objs; }
inline unsigned cnstr_scalar_size(object * o) { return to_cnstr(o)->m_scalar_size; }
inline size_t cnstr_byte_size(object * o) { return sizeof(constructor_object) + cnstr_num_objs(o)*sizeof(object*) + cnstr_scalar_size(o); } // NOLINT
inline object * cnstr_obj(object * o, unsigned i) {
    lean_assert(i < cnstr_num_objs(o));
    return obj_data<object*>(o, sizeof(constructor_object) + sizeof(object*)*i); // NOLINT
}
inline object ** cnstr_obj_cptr(object * o) {
    lean_assert(is_cnstr(o));
    return reinterpret_cast<object**>(reinterpret_cast<char*>(o) + sizeof(constructor_object));
}
template<typename T>
inline T cnstr_scalar(object * o, size_t offset) {
    return obj_data<T>(o, sizeof(constructor_object) + offset);
}
inline unsigned char * cnstr_scalar_cptr(object * o) {
    lean_assert(is_cnstr(o));
    return reinterpret_cast<unsigned char*>(reinterpret_cast<char*>(o) + sizeof(constructor_object) + cnstr_num_objs(o)*sizeof(object*)); // NOLINT
}
inline void cnstr_set_obj(object * o, unsigned i, object * v) {
    lean_assert(i < cnstr_num_objs(o));
    obj_set_data(o, sizeof(constructor_object) + sizeof(object*)*i, v); // NOLINT
}
template<typename T>
inline void cnstr_set_scalar(object * o, unsigned i, T v) {
    obj_set_data(o, sizeof(constructor_object) + i, v);
}

inline unsigned obj_tag(object * o) { if (is_scalar(o)) return unbox(o); else return cnstr_tag(o); }

/* Closures */
inline object * alloc_closure(lean_cfun fun, unsigned arity, unsigned num_fixed) {
    lean_assert(arity > 0);
    lean_assert(num_fixed < arity);
    return new (malloc(sizeof(closure_object) + num_fixed * sizeof(object *))) closure_object(fun, arity, num_fixed); // NOLINT
}
inline lean_cfun closure_fun(object * o) { return to_closure(o)->m_fun; }
inline unsigned closure_arity(object * o) { return to_closure(o)->m_arity; }
inline unsigned closure_num_fixed(object * o) { return to_closure(o)->m_num_fixed; }
inline size_t closure_byte_size(object * o) { return sizeof(closure_object) + (closure_arity(o) - 1)*sizeof(object*); } // NOLINT
inline object * closure_arg(object * o, unsigned i) {
    lean_assert(i < closure_num_fixed(o));
    return obj_data<object*>(o, sizeof(closure_object) + sizeof(object*)*i); // NOLINT
}

inline object ** closure_arg_cptr(object * o) {
    lean_assert(is_closure(o));
    return reinterpret_cast<object**>(reinterpret_cast<char*>(o) + sizeof(closure_object));
}
inline void closure_set_arg(object * o, unsigned i, object * a) {
    lean_assert(i < closure_num_fixed(o));
    obj_set_data(o, sizeof(closure_object) + sizeof(object*)*i, a); // NOLINT
}

/* Array of objects */
inline object * alloc_array(size_t size, size_t capacity) {
    return new (malloc(sizeof(array_object) + capacity * sizeof(object *))) array_object(size, capacity); // NOLINT
}
inline size_t array_size(object * o) { return to_array(o)->m_size; }
inline size_t array_capacity(object * o) { return to_array(o)->m_capacity; }
inline size_t array_byte_size(object * o) { return sizeof(array_object) + array_capacity(o)*sizeof(object*); } // NOLINT
inline object * array_obj(object * o, size_t i) {
    lean_assert(i < array_size(o));
    return obj_data<object*>(o, sizeof(array_object) + sizeof(object*)*i); // NOLINT
}
inline object ** array_cptr(object * o) {
    lean_assert(is_array(o));
    return reinterpret_cast<object**>(reinterpret_cast<char*>(o) + sizeof(array_object));
}
inline void array_set_size(object * o, size_t sz) {
    lean_assert(is_array(o));
    lean_assert(!is_shared(o));
    lean_assert(sz <= array_capacity(o));
    to_array(o)->m_size = sz;
}
inline void array_set_obj(object * o, size_t i, object * v) {
    lean_assert(i < array_size(o));
    obj_set_data(o, sizeof(array_object) + sizeof(object*)*i, v); // NOLINT
}

/* Array of scalars */
inline object * alloc_sarray(unsigned elem_size, size_t size, size_t capacity) {
    return new (malloc(sizeof(sarray_object) + capacity * elem_size)) sarray_object(elem_size, size, capacity); // NOLINT
}
inline unsigned sarray_elem_size(object * o) { return to_sarray(o)->m_elem_size; }
inline size_t sarray_size(object * o) { return to_sarray(o)->m_size; }
inline size_t sarray_capacity(object * o) { return to_sarray(o)->m_capacity; }
inline size_t sarray_byte_size(object * o) { return sizeof(sarray_object) + sarray_capacity(o)*sarray_elem_size(o); } // NOLINT
template<typename T>
T * sarray_cptr_core(object * o) { lean_assert(is_sarray(o)); return reinterpret_cast<T*>(reinterpret_cast<char*>(o) + sizeof(sarray_object)); }
template<typename T>
T * sarray_cptr(object * o) { lean_assert(sarray_elem_size(o) == sizeof(T)); return sarray_cptr_core<T>(o); }
template<typename T> T sarray_data(object * o, size_t i) { return sarray_cptr<T>(o)[i]; }
template<typename T> void sarray_set_data(object * o, size_t i, T v) {
    obj_set_data(o, sizeof(sarray_object) + sizeof(T)*i, v);
}
inline void sarray_set_size(object * o, size_t sz) {
    lean_assert(is_sarray(o));
    lean_assert(!is_shared(o));
    lean_assert(sz <= sarray_capacity(o));
    to_sarray(o)->m_size = sz;
}

/* MPZ */

inline object * alloc_mpz(mpz const & m) { return new mpz_object(m); }
inline mpz const & mpz_value(object * o) { return to_mpz(o)->m_value; }

/* String */
inline object * alloc_string(size_t size, size_t capacity, size_t len) {
    return new (malloc(sizeof(string_object) + capacity)) string_object(size, capacity, len); // NOLINT
}
object * mk_string(char const * s);
object * mk_string(std::string const & s);
inline char const * string_data(object * o) { lean_assert(is_string(o)); return reinterpret_cast<char*>(o) + sizeof(string_object); }
inline size_t string_capacity(object * o) { return to_string(o)->m_capacity; }
inline size_t string_size(object * o) { return to_string(o)->m_size; }
inline size_t string_len(object * o) { return to_string(o)->m_length; }
inline size_t string_byte_size(object * o) { return sizeof(string_object) + string_capacity(o); } // NOLINT
object * string_push(object * s, unsigned c);
object * string_append(object * s1, object * s2);
bool string_eq(object * s1, object * s2);
inline bool string_ne(object * s1, object * s2) { return !string_eq(s1, s2); }
bool string_eq(object * s1, char const * s2);
bool string_lt(object * s1, object * s2);

/* Natural numbers */

#define LEAN_MAX_SMALL_NAT (sizeof(void*) == 8 ? std::numeric_limits<unsigned>::max() : (std::numeric_limits<unsigned>::max() >> 1)) // NOLINT

inline object * mk_nat_obj_core(mpz const & m) {
    lean_assert(m > LEAN_MAX_SMALL_NAT);
    return alloc_mpz(m);
}

inline object * mk_nat_obj(mpz const & m) {
    if (m > LEAN_MAX_SMALL_NAT)
        return mk_nat_obj_core(m);
    else
        return box(m.get_unsigned_int());
}

inline object * mk_nat_obj(unsigned n) {
    if (sizeof(void*) == 8) { // NOLINT
        return box(n);
    } else if (n <= LEAN_MAX_SMALL_NAT) {
        return box(n);
    } else {
        return mk_nat_obj_core(mpz(n));
    }
}

inline object * mk_nat_obj(uint64 n) {
    if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT)) {
        return box(n);
    } else {
        return mk_nat_obj_core(mpz(n));
    }
}

inline uint64 nat2uint64(object * a) {
    lean_assert(is_scalar(a));
    return unbox(a);
}

inline object * nat_succ(object * a) {
    if (LEAN_LIKELY(is_scalar(a))) {
        return mk_nat_obj(nat2uint64(a) + 1);
    } else {
        return mk_nat_obj_core(mpz_value(a) + 1);
    }
}

object * nat_big_add(object * a1, object * a2);

inline object * nat_add(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_nat_obj(nat2uint64(a1) + nat2uint64(a2));
    } else {
        return nat_big_add(a1, a2);
    }
}

object * nat_big_sub(object * a1, object * a2);

inline object * nat_sub(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        unsigned n1 = unbox(a1);
        unsigned n2 = unbox(a2);
        if (n1 < n2)
            return box(0);
        else
            return box(n1 - n2);
    } else {
        return nat_big_sub(a1, a2);
    }
}

object * nat_big_mul(object * a1, object * a2);

inline object * nat_mul(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_nat_obj(nat2uint64(a1) * nat2uint64(a2));
    } else {
        return nat_big_mul(a1, a2);
    }
}

object * nat_big_div(object * a1, object * a2);

inline object * nat_div(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        unsigned n1 = unbox(a1);
        unsigned n2 = unbox(a2);
        if (n2 == 0)
            return box(0);
        else
            return box(n1 / n2);
    } else {
        return nat_big_div(a1, a2);
    }
}

object * nat_big_mod(object * a1, object * a2);

inline object * nat_mod(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        unsigned n1 = unbox(a1);
        unsigned n2 = unbox(a2);
        if (n2 == 0)
            return box(0);
        else
            return box(n1 % n2);
    } else {
        return nat_big_mod(a1, a2);
    }
}

bool nat_big_eq(object * a1, object * a2);

inline bool nat_eq(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 == a2;
    } else {
        return nat_big_eq(a1, a2);
    }
}

inline bool nat_ne(object * a1, object * a2) {
    return !nat_eq(a1, a2);
}

bool nat_big_le(object * a1, object * a2);

inline bool nat_le(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 <= a2;
    } else {
        return nat_big_le(a1, a2);
    }
}

bool nat_big_lt(object * a1, object * a2);

inline bool nat_lt(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 < a2;
    } else {
        return nat_big_lt(a1, a2);
    }
}

object * nat_big_land(object * a1, object * a2);

inline object * nat_land(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return reinterpret_cast<object*>(reinterpret_cast<uintptr_t>(a1) & reinterpret_cast<uintptr_t>(a2));
    } else {
        return nat_big_land(a1, a2);
    }
}

object * nat_big_lor(object * a1, object * a2);

inline object * nat_lor(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return reinterpret_cast<object*>(reinterpret_cast<uintptr_t>(a1) | reinterpret_cast<uintptr_t>(a2));
    } else {
        return nat_big_lor(a1, a2);
    }
}

object * nat_big_xor(object * a1, object * a2);

inline object * nat_lxor(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return box(unbox(a1) ^ unbox(a2));
    } else {
        return nat_big_xor(a1, a2);
    }
}

/* Integers */

#define LEAN_MAX_SMALL_INT (sizeof(void*) == 8 ? std::numeric_limits<int>::max() : (1 << 30)) // NOLINT
#define LEAN_MIN_SMALL_INT (sizeof(void*) == 8 ? std::numeric_limits<int>::min() : -(1 << 30)) // NOLINT

inline object * mk_int_obj_core(mpz const & m) {
    lean_assert(m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT);
    return alloc_mpz(m);
}

inline object * mk_int_obj(mpz const & m) {
    if (m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT)
        return mk_int_obj_core(m);
    else
        return box(static_cast<unsigned>(m.get_int()));
}

inline object * mk_int_obj(int n) {
    if (sizeof(void*) == 8) { // NOLINT
        return box(static_cast<unsigned>(n));
    } else if (LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT) {
        return box(static_cast<unsigned>(n));
    } else {
        return alloc_mpz(mpz(n));
    }
}

inline object * mk_int_obj(int64 n) {
    if (LEAN_LIKELY(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT)) {
        return box(static_cast<unsigned>(static_cast<int>(n)));
    } else {
        return mk_int_obj_core(mpz(n));
    }
}

inline int64 int2int64(object * a) {
    lean_assert(is_scalar(a));
    if (sizeof(void*) == 8) { // NOLINT
        return static_cast<int>(unbox(a));
    } else {
        return static_cast<int>(reinterpret_cast<size_t>(a)) >> 1;
    }
}

inline int int2int(object * a) {
    lean_assert(is_scalar(a));
    if (sizeof(void*) == 8) { // NOLINT
        return static_cast<int>(unbox(a));
    } else {
        return static_cast<int>(reinterpret_cast<size_t>(a)) >> 1;
    }
}

inline object * nat2int(object * a) {
    if (is_scalar(a)) {
        unsigned v = unbox(a);
        if (v <= LEAN_MAX_SMALL_INT) {
            return a;
        } else {
            return alloc_mpz(mpz(v));
        }
    } else {
        return a;
    }
}

inline object * int_neg(object * a) {
    if (LEAN_LIKELY(is_scalar(a))) {
        return mk_int_obj(-int2int64(a));
    } else {
        return mk_int_obj(neg(mpz_value(a)));
    }
}

object * int_big_add(object * a1, object * a2);

inline object * int_add(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_int_obj(int2int64(a1) + int2int64(a2));
    } else {
        return int_big_add(a1, a2);
    }
}

object * int_big_sub(object * a1, object * a2);

inline object * int_sub(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_int_obj(int2int64(a1) - int2int64(a2));
    } else {
        return int_big_sub(a1, a2);
    }
}

object * int_big_mul(object * a1, object * a2);

inline object * int_mul(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return mk_int_obj(int2int64(a1) * int2int64(a2));
    } else {
        return int_big_mul(a1, a2);
    }
}

object * int_big_div(object * a1, object * a2);

inline object * int_div(object * a1, object * a2) {
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

object * int_big_rem(object * a1, object * a2);

inline object * int_rem(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        int v1 = int2int(a1);
        int v2 = int2int(a2);
        if (v2 == 0)
            return box(0);
        else
            return mk_int_obj(v1 % v2);
    } else {
        return int_big_rem(a1, a2);
    }
}

bool int_big_eq(object * a1, object * a2);

inline bool int_eq(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return a1 == a2;
    } else {
        return int_big_eq(a1, a2);
    }
}

inline bool int_ne(object * a1, object * a2) {
    return !int_eq(a1, a2);
}

bool int_big_le(object * a1, object * a2);

inline bool int_le(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return int2int(a1) <= int2int(a2);
    } else {
        return int_big_le(a1, a2);
    }
}

bool int_big_lt(object * a1, object * a2);

inline bool int_lt(object * a1, object * a2) {
    if (LEAN_LIKELY(is_scalar(a1) && is_scalar(a2))) {
        return int2int(a1) < int2int(a2);
    } else {
        return int_big_lt(a1, a2);
    }
}
}
