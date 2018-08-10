/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include <algorithm>
#include "runtime/object.h"
#include "runtime/utf8.h"
#include "runtime/apply.h"

namespace lean {
size_t obj_byte_size(object * o) {
    switch (get_kind(o)) {
    case object_kind::Constructor:     return cnstr_byte_size(o);
    case object_kind::Closure:         return closure_byte_size(o);
    case object_kind::Array:           return array_byte_size(o);
    case object_kind::ScalarArray:     return sarray_byte_size(o);
    case object_kind::String:          return string_byte_size(o);
    case object_kind::MPZ:             return sizeof(mpz_object);
    case object_kind::Thunk:           return sizeof(thunk_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

size_t obj_header_size(object * o) {
    switch (get_kind(o)) {
    case object_kind::Constructor:     return sizeof(constructor_object);
    case object_kind::Closure:         return sizeof(closure_object);
    case object_kind::Array:           return sizeof(array_object);
    case object_kind::ScalarArray:     return sizeof(sarray_object);
    case object_kind::String:          return sizeof(string_object);
    case object_kind::MPZ:             return sizeof(mpz_object);
    case object_kind::Thunk:           return sizeof(thunk_object);
    case object_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

/* We use the field m_rc to implement a linked list of lean objects to be deleted.
   This hack is safe because m_rc has type uintptr_t. */

static_assert(sizeof(atomic<rc_type>) == sizeof(object*),  "unexpected atomic<rc_type> size, the object GC assumes these two types have the same size"); // NOLINT

inline object * get_next(object * o) {
    lean_assert(o == static_cast<void*>(&(o->m_rc))); // The object GC relies on the fact that the first field of a structure is stored at offset 0
    return *reinterpret_cast<object**>(o);
}

inline void set_next(object * o, object * n) {
    lean_assert(o == static_cast<void*>(&(o->m_rc))); // The object GC relies on the fact that the first field of a structure is stored at offset 0
    *reinterpret_cast<object**>(o) = n;
}

inline void push_back(object * & todo, object * v) {
    set_next(v, todo);
    todo = v;
}

inline object * pop_back(object * & todo) {
    object * r = todo;
    todo = get_next(todo);
    return r;
}

inline void dec(object * o, object* & todo) {
    if (!is_scalar(o) && dec_ref_core(o))
        push_back(todo, o);
}

void del(object * o) {
    object * todo = nullptr;
    while (true) {
        switch (get_kind(o)) {
        case object_kind::Constructor: {
            object ** it  = cnstr_obj_cptr(o);
            object ** end = it + cnstr_num_objs(o);
            for (; it != end; ++it) dec(*it, todo);
            free(o);
            break;
        }
        case object_kind::Closure: {
            object ** it  = closure_arg_cptr(o);
            object ** end = it + closure_num_fixed(o);
            for (; it != end; ++it) dec(*it, todo);
            free(o);
            break;
        }
        case object_kind::Array: {
            object ** it  = array_cptr(o);
            object ** end = it + array_size(o);
            for (; it != end; ++it) dec(*it, todo);
            free(o);
            break;
        }
        case object_kind::ScalarArray:
            free(o); break;
        case object_kind::String:
            free(o); break;
        case object_kind::MPZ:
            dealloc_mpz(o); break;
        case object_kind::Thunk:
            dec(to_thunk(o)->m_closure, todo);
            if (object * v = to_thunk(o)->m_value) dec(v, todo);
            free(o);
            break;
        case object_kind::External:
            dealloc_external(o); break;
        }
        /* We can use a counter to avoid pauses at `del` when many objects
           are reachable from `o` need to be deleted.
           The idea is to have a threshold on the maximum number of elements
           that can be deleted in a single round. */
        if (todo == nullptr)
            return;
        o = pop_back(todo);
    }
}

/* Scalar arrays */

#if 0
static object * sarray_ensure_capacity(object * o, size_t extra) {
    lean_assert(!is_shared(o));
    size_t sz  = sarray_size(o);
    size_t cap = sarray_capacity(o);
    if (sz + extra > cap) {
        unsigned esize = sarray_elem_size(o);
        object * new_o = alloc_sarray(esize, sz, cap + sz + extra);
        lean_assert(sarray_capacity(new_o) >= sz + extra);
        memcpy(sarray_cptr<char>(new_o), sarray_cptr<char>(o), esize * sz);
        free(o);
        return new_o;
    } else {
        return o;
    }
}
#endif

/* Strings */
static inline char * w_string_data(object * o) { lean_assert(is_string(o)); return reinterpret_cast<char *>(o) + sizeof(string_object); }

static object * string_ensure_capacity(object * o, size_t extra) {
    lean_assert(!is_shared(o));
    size_t sz  = string_size(o);
    size_t cap = string_capacity(o);
    if (sz + extra > cap) {
        object * new_o = alloc_string(sz, cap + sz + extra, string_len(o));
        lean_assert(string_capacity(new_o) >= sz + extra);
        memcpy(w_string_data(new_o), string_data(o), sz);
        free(o);
        return new_o;
    } else {
        return o;
    }
}

object * mk_string(char const * s) {
    size_t sz  = strlen(s);
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_data(r), s, sz+1);
    return r;
}

object * mk_string(std::string const & s) {
    size_t sz  = s.size();
    size_t len = utf8_strlen(s);
    size_t rsz = sz + 1;
    object * r = alloc_string(rsz, rsz, len);
    memcpy(w_string_data(r), s.data(), sz);
    w_string_data(r)[sz] = 0;
    return r;
}

object * string_push(object * s, unsigned c) {
    lean_assert(!is_shared(s));
    object * r = string_ensure_capacity(s, 5);
    size_t sz  = string_size(r);
    unsigned consumed = push_unicode_scalar(w_string_data(r) + sz - 1, c);
    to_string(r)->m_size   = sz + consumed;
    to_string(r)->m_length++;
    w_string_data(r)[sz + consumed - 1] = 0;
    return r;
}

object * string_append(object * s1, object * s2) {
    lean_assert(!is_shared(s1));
    size_t sz1 = string_size(s1);
    size_t sz2 = string_size(s2);
    size_t len1 = string_len(s1);
    size_t len2 = string_len(s2);
    object * r = string_ensure_capacity(s1, sz2-1);
    if (s1 == s2) s2 = r;
    memcpy(w_string_data(r) + sz1 - 1, string_data(s2), sz2 - 1);
    unsigned new_sz = sz1 + sz2 - 1;
    to_string(r)->m_size   = new_sz;
    to_string(r)->m_length = len1 + len2;
    w_string_data(r)[new_sz - 1] = 0;
    return r;
}

bool string_eq(object * s1, object * s2) {
    if (string_size(s1) != string_size(s2))
        return false;
    return std::memcmp(string_data(s1), string_data(s2), string_size(s1)) == 0;
}

bool string_eq(object * s1, char const * s2) {
    if (string_size(s1) != strlen(s2) + 1)
        return false;
    return std::memcmp(string_data(s1), s2, string_size(s1)) == 0;
}

bool string_lt(object * s1, object * s2) {
    size_t sz1 = string_size(s1) - 1; // ignore null char in the end
    size_t sz2 = string_size(s2) - 1; // ignore null char in the end
    int r      = std::memcmp(string_data(s1), string_data(s2), std::min(sz1, sz2));
    return r < 0 || (r == 0 && sz1 < sz2);
}

/* Natural numbers */

object * nat_big_add(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj_core(unbox(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj_core(mpz_value(a1) + unbox(a2));
    else
        return mk_nat_obj_core(mpz_value(a1) + mpz_value(a2));
}

object * nat_big_sub(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return box(0);
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return mk_nat_obj(mpz_value(a1) - unbox(a2));
    } else {
        if (mpz_value(a1) < mpz_value(a2))
            return box(0);
        else
            return mk_nat_obj(mpz_value(a1) - mpz_value(a2));
    }
}

object * nat_big_mul(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj_core(unbox(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj_core(mpz_value(a1) * unbox(a2));
    else
        return mk_nat_obj_core(mpz_value(a1) * mpz_value(a2));
}

object * nat_big_div(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        lean_assert(unbox(a1) / mpz_value(a2) == 0);
        return box(0);
    } else if (is_scalar(a2)) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : mk_nat_obj(mpz_value(a1) / n2);
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_nat_obj(mpz_value(a1) / mpz_value(a2));
    }
}

object * nat_big_mod(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        return a1;
    } else if (is_scalar(a2)) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : box((mpz_value(a1) % mpz(n2)).get_unsigned_int());
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_nat_obj(mpz_value(a1) % mpz_value(a2));
    }
}

bool nat_big_eq(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) != mpz_value(a2))
        return false;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) != unbox(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

bool nat_big_le(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2))
        return true;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return false;
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

bool nat_big_lt(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return true;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return false;
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

object * nat_big_land(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) & mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) & mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) & mpz_value(a2));
}

object * nat_big_lor(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) | mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) | mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) | mpz_value(a2));
}

object * nat_big_lxor(object * a1, object * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_nat_obj(mpz(unbox(a1)) ^ mpz_value(a2));
    else if (is_scalar(a2))
        return mk_nat_obj(mpz_value(a1) ^ mpz(unbox(a2)));
    else
        return mk_nat_obj(mpz_value(a1) ^ mpz_value(a2));
}

/* Integers */

object * int_big_add(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) + int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) + mpz_value(a2));
}

object * int_big_sub(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) - mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) - int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) - mpz_value(a2));
}

object * int_big_mul(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) * int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) * mpz_value(a2));
}

object * int_big_div(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(int2int(a1) / mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) / int2int(a2));
    else
        return mk_int_obj(mpz_value(a1) / mpz_value(a2));
}

object * int_big_rem(object * a1, object * a2) {
    if (is_scalar(a1))
        return mk_int_obj(mpz(int2int(a1)) % mpz_value(a2));
    else if (is_scalar(a2))
        return mk_int_obj(mpz_value(a1) % mpz(int2int(a2)));
    else
        return mk_int_obj(mpz_value(a1) % mpz_value(a2));
}

bool int_big_eq(object * a1, object * a2) {
    if (is_scalar(a1)) {
        lean_assert(int2int(a1) != mpz_value(a2))
        return false;
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) != int2int(a2))
        return false;
    } else {
        return mpz_value(a1) == mpz_value(a2);
    }
}

bool int_big_le(object * a1, object * a2) {
    if (is_scalar(a1)) {
        return int2int(a1) <= mpz_value(a2);
    } else if (is_scalar(a2)) {
        return mpz_value(a1) <= int2int(a2);
    } else {
        return mpz_value(a1) <= mpz_value(a2);
    }
}

bool int_big_lt(object * a1, object * a2) {
    if (is_scalar(a1)) {
        return int2int(a1) < mpz_value(a2);
    } else if (is_scalar(a2)) {
        return mpz_value(a1) < int2int(a2);
    } else {
        return mpz_value(a1) < mpz_value(a2);
    }
}

/* Debugging helper functions */

void dbg_print_str(object * o) {
    lean_assert(is_string(o));
    std::cout << string_data(o) << "\n";
}

void dbg_print_num(object * o) {
    if (is_scalar(o)) {
        std::cout << unbox(o) << "\n";
    } else {
        std::cout << mpz_value(o) << "\n";
    }
}
}

extern "C" void lean_dbg_print_str(lean::object* o) { lean::dbg_print_str(o); }
extern "C" void lean_dbg_print_num(lean::object* o) { lean::dbg_print_num(o); }
