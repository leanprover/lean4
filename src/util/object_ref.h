/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "runtime/object.h"

namespace lean {
/* Smart point for Lean objects. It is useful for writing C++ code that manipulates Lean objects.  */
class object_ref {
    object * m_obj;
public:
    object_ref():m_obj(box(0)) {}
    explicit object_ref(object * o):m_obj(o) { lean_assert(is_scalar(o) || get_rc(o) > 0); }
    object_ref(object_ref const & s):m_obj(s.m_obj) { inc(m_obj); }
    object_ref(object_ref && s):m_obj(s.m_obj) { s.m_obj = box(0); }
    ~object_ref() { dec(m_obj); }
    object_ref & operator=(object_ref const & s) {
        inc(s.m_obj);
        object * new_obj = s.m_obj;
        dec(m_obj);
        m_obj = new_obj;
        return *this;
    }
    object_ref & operator=(object_ref && s) {
        dec(m_obj);
        m_obj   = s.m_obj;
        s.m_obj = box(0);
        return *this;
    }
    object * raw() const { return m_obj; }
    static void swap(object_ref & a, object_ref & b) { std::swap(a.m_obj, b.m_obj); }
};

/* Remark: this function doesn't increase the reference counter of objs */
object_ref mk_cnstr(unsigned tag, unsigned num_objs, object ** objs, unsigned scalar_sz = 0);
inline object_ref mk_cnstr(unsigned tag, object * o, unsigned scalar_sz = 0) { return mk_cnstr(tag, 1, &o, scalar_sz); }
inline object_ref mk_cnstr(unsigned tag, object * o1, object * o2, unsigned scalar_sz = 0) {
    object * os[2] = { o1, o2 };
    return mk_cnstr(tag, 2, os, scalar_sz);
}
inline object_ref mk_cnstr(unsigned tag, object * o1, object * o2, object * o3, unsigned scalar_sz = 0) {
    object * os[3] = { o1, o2, o3 };
    return mk_cnstr(tag, 3, os, scalar_sz);
}
inline object_ref mk_cnstr(unsigned tag, object * o1, object * o2, object * o3, object * o4, unsigned scalar_sz = 0) {
    object * os[4] = { o1, o2, o3, o4 };
    return mk_cnstr(tag, 4, os, scalar_sz);
}

/* The following definition is a low level hack that relies on the fact that sizeof(object_ref) == sizeof(object *). */
inline object_ref const & cnstr_obj_ref(object * o, unsigned i) {
    static_assert(sizeof(object_ref) == sizeof(object *), "unexpected object_ref size"); // NOLINT
    lean_assert(is_cnstr(o));
    return reinterpret_cast<object_ref const *>(reinterpret_cast<char*>(o) + sizeof(constructor_object))[i];
}

inline object_ref const & cnstr_obj_ref(object_ref const & ref, unsigned i) {
    return cnstr_obj_ref(ref.raw(), i);
}
}
