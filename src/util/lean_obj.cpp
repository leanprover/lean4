/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lean_obj.h"
#include "util/buffer.h"

namespace lean {
size_t obj_byte_size(lean_obj * o) {
    switch (get_kind(o)) {
    case lean_obj_kind::Constructor:     return cnstr_byte_size(o);
    case lean_obj_kind::Closure:         return closure_byte_size(o);
    case lean_obj_kind::Array:           return array_byte_size(o);
    case lean_obj_kind::ScalarArray:     return sarray_byte_size(o);
    case lean_obj_kind::String:          return string_byte_size(o);
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
    case lean_obj_kind::String:          return sizeof(lean_string);
    case lean_obj_kind::MPZ:             return sizeof(lean_mpz);
    case lean_obj_kind::External:        lean_unreachable();
    }
    lean_unreachable();
}

/* We use the field m_rc to implement a linked list of lean objects to be deleted.
   This hack is safe because m_rc has type uintptr_t. */

static_assert(sizeof(atomic<rc_type>) == sizeof(lean_obj*),  "unexpected atomic<rc_type> size, the object GC assumes these two types have the same size");

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
        case lean_obj_kind::String:
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
}
