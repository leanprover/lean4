/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include "runtime/lean_obj.h"
#include "runtime/utf8.h"

namespace lean {
size_t obj_byte_size(lean_obj * o) {
    switch (get_kind(o)) {
    case lean_obj_kind::Constructor:     return cnstr_byte_size(o);
    case lean_obj_kind::Closure:         return closure_byte_size(o);
    case lean_obj_kind::Array:           return array_byte_size(o);
    case lean_obj_kind::ScalarArray:     return sarray_byte_size(o);
    case lean_obj_kind::MPZ:             return sizeof(lean_mpz);
    case lean_obj_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

size_t obj_header_size(lean_obj * o) {
    switch (get_kind(o)) {
    case lean_obj_kind::Constructor:     return sizeof(lean_cnstr);
    case lean_obj_kind::Closure:         return sizeof(lean_closure);
    case lean_obj_kind::Array:           return sizeof(lean_array);
    case lean_obj_kind::ScalarArray:     return sizeof(lean_sarray);
    case lean_obj_kind::MPZ:             return sizeof(lean_mpz);
    case lean_obj_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

/* We use the field m_rc to implement a linked list of lean objects to be deleted.
   This hack is safe because m_rc has type uintptr_t. */

static_assert(sizeof(atomic<rc_type>) == sizeof(lean_obj*),  "unexpected atomic<rc_type> size, the object GC assumes these two types have the same size"); // NOLINT

inline lean_obj * get_next(lean_obj * o) {
    lean_assert(o == static_cast<void*>(&(o->m_rc))); // The object GC relies on the fact that the first field of a structure is stored at offset 0
    return *reinterpret_cast<lean_obj**>(o);
}

inline void set_next(lean_obj * o, lean_obj * n) {
    lean_assert(o == static_cast<void*>(&(o->m_rc))); // The object GC relies on the fact that the first field of a structure is stored at offset 0
    *reinterpret_cast<lean_obj**>(o) = n;
}

inline void push_back(lean_obj * & todo, lean_obj * v) {
    set_next(v, todo);
    todo = v;
}

inline lean_obj * pop_back(lean_obj * & todo) {
    lean_obj * r = todo;
    todo = get_next(todo);
    return r;
}

inline void dec_ref(lean_obj * o, lean_obj* & todo) {
    if (!is_scalar(o) && dec_ref_core(o))
        push_back(todo, o);
}

void del(lean_obj * o) {
    lean_obj * todo = nullptr;
    while (true) {
        switch (get_kind(o)) {
        case lean_obj_kind::Constructor: {
            lean_obj ** it  = cnstr_obj_cptr(o);
            lean_obj ** end = it + cnstr_num_objs(o);
            for (; it != end; ++it) dec_ref(*it, todo);
            free(o);
            break;
        }
        case lean_obj_kind::Closure: {
            lean_obj ** it  = closure_arg_cptr(o);
            lean_obj ** end = it + closure_num_fixed(o);
            for (; it != end; ++it) dec_ref(*it, todo);
            free(o);
            break;
        }
        case lean_obj_kind::Array: {
            lean_obj ** it  = array_cptr(o);
            lean_obj ** end = it + array_size(o);
            for (; it != end; ++it) dec_ref(*it, todo);
            free(o);
            break;
        }
        case lean_obj_kind::ScalarArray:
            free(o); break;
        case lean_obj_kind::MPZ:
            dealloc_mpz(o); break;
        case lean_obj_kind::External:
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

static lean_obj * sarray_ensure_capacity(lean_obj * o, size_t extra) {
    lean_assert(!is_shared(o));
    size_t sz  = sarray_size(o);
    size_t cap = sarray_capacity(o);
    if (sz + extra > cap) {
        unsigned esize = sarray_elem_size(o);
        lean_obj * new_o = alloc_sarray(esize, sz, cap + sz + extra);
        lean_assert(sarray_capacity(new_o) >= sz + extra);
        memcpy(sarray_cptr<char>(new_o), sarray_cptr<char>(o), esize * sz);
        free(o);
        return new_o;
    } else {
        return o;
    }
}

/* Strings */

lean_obj * mk_string(char const * s) {
    size_t sz  = strlen(s);
    size_t len = utf8_strlen(s);
    size_t rsz = sz + sizeof(size_t) + 1;
    lean_obj * r = alloc_sarray(1, rsz, rsz);
    set_sarray_data<size_t>(r, 0, len);
    memcpy(sarray_cptr<char>(r) + sizeof(size_t), s, sz+1);
    return r;
}

lean_obj * mk_string(std::string const & s) {
    return mk_string(s.c_str());
}

lean_obj * string_push(lean_obj * s, unsigned c) {
    lean_assert(!is_shared(s));
    lean_obj * r = sarray_ensure_capacity(s, 5);
    size_t sz = sarray_size(r);
    unsigned consumed = push_unicode_scalar(sarray_cptr<char>(r) + sz - 1, c);
    set_sarray_size(r, sz + consumed);
    set_sarray_data<char>(r, sz + consumed - 1, 0);
    set_sarray_data<size_t>(r, 0, string_len(r) + 1);
    return r;
}

lean_obj * string_append(lean_obj * s1, lean_obj * s2) {
    lean_assert(!is_shared(s1));
    size_t sz1 = sarray_size(s1);
    size_t sz2 = sarray_size(s2);
    size_t len1 = string_len(s1);
    size_t len2 = string_len(s2);
    lean_assert(sz2 >= sizeof(size_t));
    sz2 -= sizeof(size_t);
    lean_obj * r = sarray_ensure_capacity(s1, sz2-1);
    if (s1 == s2) s2 = r;
    memcpy(sarray_cptr<char>(r) + sz1 - 1, c_str(s2), sz2 - 1);
    unsigned new_sz = sz1 + sz2 - 1;
    set_sarray_size(r, new_sz);
    set_sarray_data<char>(r, new_sz - 1, 0);
    set_sarray_data<size_t>(r, 0, len1 + len2);
    return r;
}

/* Natural numbers */

lean_obj * nat_big_add(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_mpz_core(unbox(a1) + mpz_value(a2));
    else if (is_scalar(a2))
        return mk_mpz_core(mpz_value(a1) + unbox(a2));
    else
        return mk_mpz_core(mpz_value(a1) + mpz_value(a2));
}

lean_obj * nat_big_sub(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(unbox(a1) < mpz_value(a2));
        return box(0);
    } else if (is_scalar(a2)) {
        lean_assert(mpz_value(a1) > unbox(a2));
        return mk_mpz(mpz_value(a1) - unbox(a2));
    } else {
        if (mpz_value(a1) < mpz_value(a2))
            return box(0);
        else
            return mk_mpz(mpz_value(a1) - mpz_value(a2));
    }
}

lean_obj * nat_big_mul(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_mpz_core(unbox(a1) * mpz_value(a2));
    else if (is_scalar(a2))
        return mk_mpz_core(mpz_value(a1) * unbox(a2));
    else
        return mk_mpz_core(mpz_value(a1) * mpz_value(a2));
}

lean_obj * nat_big_div(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        lean_assert(unbox(a1) / mpz_value(a2) == 0);
        return box(0);
    } else if (is_scalar(a2)) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : mk_mpz(mpz_value(a1) / n2);
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_mpz(mpz_value(a1) / mpz_value(a2));
    }
}

lean_obj * nat_big_mod(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1)) {
        lean_assert(mpz_value(a2) != 0);
        return a1;
    } else if (is_scalar(a2)) {
        unsigned n2 = unbox(a2);
        return n2 == 0 ? a2 : box((mpz_value(a1) % mpz(n2)).get_unsigned_int());
    } else {
        lean_assert(mpz_value(a2) != 0);
        return mk_mpz(mpz_value(a1) % mpz_value(a2));
    }
}

bool nat_big_eq(lean_obj * a1, lean_obj * a2) {
    if (is_scalar(a1))
        return unbox(a1) == mpz_value(a2);
    else if (is_scalar(a2))
        return mpz_value(a1) == unbox(a2);
    else
        return mpz_value(a1) == mpz_value(a2);
}

bool nat_big_le(lean_obj * a1, lean_obj * a2) {
    if (is_scalar(a1))
        return unbox(a1) <= mpz_value(a2);
    else if (is_scalar(a2))
        return mpz_value(a1) <= unbox(a2);
    else
        return mpz_value(a1) <= mpz_value(a2);
}

bool nat_big_lt(lean_obj * a1, lean_obj * a2) {
    if (is_scalar(a1))
        return unbox(a1) < mpz_value(a2);
    else if (is_scalar(a2))
        return mpz_value(a1) < unbox(a2);
    else
        return mpz_value(a1) < mpz_value(a2);
}

lean_obj * nat_big_land(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_mpz(mpz(unbox(a1)) & mpz_value(a2));
    else if (is_scalar(a2))
        return mk_mpz(mpz_value(a1) & mpz(unbox(a2)));
    else
        return mk_mpz(mpz_value(a1) & mpz_value(a2));
}

lean_obj * nat_big_lor(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_mpz(mpz(unbox(a1)) | mpz_value(a2));
    else if (is_scalar(a2))
        return mk_mpz(mpz_value(a1) | mpz(unbox(a2)));
    else
        return mk_mpz(mpz_value(a1) | mpz_value(a2));
}

lean_obj * nat_big_lxor(lean_obj * a1, lean_obj * a2) {
    lean_assert(!is_scalar(a1) || !is_scalar(a2));
    if (is_scalar(a1))
        return mk_mpz(mpz(unbox(a1)) ^ mpz_value(a2));
    else if (is_scalar(a2))
        return mk_mpz(mpz_value(a1) ^ mpz(unbox(a2)));
    else
        return mk_mpz(mpz_value(a1) ^ mpz_value(a2));
}

/* Debugging helper functions */

void dbg_print_str(lean_obj * o) {
    lean_assert(is_string(o));
    std::cout << c_str(o) << "\n";
}

void dbg_print_num(lean_obj * o) {
    if (is_scalar(o)) {
        std::cout << unbox(o) << "\n";
    } else {
        std::cout << mpz_value(o) << "\n";
    }
}
}

extern "C" void lean_dbg_print_str(lean::lean_obj* o) { lean::dbg_print_str(o); }
extern "C" void lean_dbg_print_num(lean::lean_obj* o) { lean::dbg_print_num(o); }
