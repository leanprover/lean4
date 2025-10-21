/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <string>
#include "runtime/object.h"
#include "runtime/optional.h"

namespace lean {
/* Smart point for Lean objects. It is useful for writing C++ code that manipulates Lean objects.  */
class object_ref {
protected:
    object * m_obj;
public:
    object_ref():m_obj(box(0)) {}
    explicit object_ref(obj_arg o):m_obj(o) {}
    object_ref(b_obj_arg o, bool):m_obj(o) { inc(o); }
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
    void set_box(object * o) {
        lean_assert(is_scalar(m_obj));
        m_obj = o;
    }
    object * raw() const { return m_obj; }
    object * steal() { object * r = m_obj; m_obj = box(0); return r; }
    object * to_obj_arg() const { inc(m_obj); return m_obj; }
    static void swap(object_ref & a, object_ref & b) { std::swap(a.m_obj, b.m_obj); }
};

/* Remark: this function doesn't increase the reference counter of objs */
LEAN_EXPORT object_ref mk_cnstr(unsigned tag, unsigned num_objs, object ** objs, unsigned scalar_sz = 0);
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
inline object_ref mk_cnstr(unsigned tag, object * o1, object * o2, object * o3, object * o4, object * o5, unsigned scalar_sz = 0) {
    object * os[5] = { o1, o2, o3, o4, o5 };
    return mk_cnstr(tag, 5, os, scalar_sz);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 1, scalar_sz);
    cnstr_set(r, 0, o.to_obj_arg());
    return object_ref(r);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o1, object_ref const & o2, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 2, scalar_sz);
    cnstr_set(r, 0, o1.to_obj_arg());
    cnstr_set(r, 1, o2.to_obj_arg());
    return object_ref(r);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o1, object_ref const & o2, object_ref const & o3, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 3, scalar_sz);
    cnstr_set(r, 0, o1.to_obj_arg());
    cnstr_set(r, 1, o2.to_obj_arg());
    cnstr_set(r, 2, o3.to_obj_arg());
    return object_ref(r);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o1, object_ref const & o2, object_ref const & o3, object_ref const & o4, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 4, scalar_sz);
    cnstr_set(r, 0, o1.to_obj_arg());
    cnstr_set(r, 1, o2.to_obj_arg());
    cnstr_set(r, 2, o3.to_obj_arg());
    cnstr_set(r, 3, o4.to_obj_arg());
    return object_ref(r);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o1, object_ref const & o2, object_ref const & o3, object_ref const & o4, object_ref const & o5, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 5, scalar_sz);
    cnstr_set(r, 0, o1.to_obj_arg());
    cnstr_set(r, 1, o2.to_obj_arg());
    cnstr_set(r, 2, o3.to_obj_arg());
    cnstr_set(r, 3, o4.to_obj_arg());
    cnstr_set(r, 4, o5.to_obj_arg());
    return object_ref(r);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o1, object_ref const & o2, object_ref const & o3, object_ref const & o4, object_ref const & o5, object_ref const & o6, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 6, scalar_sz);
    cnstr_set(r, 0, o1.to_obj_arg());
    cnstr_set(r, 1, o2.to_obj_arg());
    cnstr_set(r, 2, o3.to_obj_arg());
    cnstr_set(r, 3, o4.to_obj_arg());
    cnstr_set(r, 4, o5.to_obj_arg());
    cnstr_set(r, 5, o6.to_obj_arg());
    return object_ref(r);
}

inline object_ref mk_cnstr(unsigned tag, object_ref const & o1, object_ref const & o2, object_ref const & o3, object_ref const & o4, object_ref const & o5, object_ref const & o6, object_ref const & o7, unsigned scalar_sz = 0) {
    object * r = alloc_cnstr(tag, 7, scalar_sz);
    cnstr_set(r, 0, o1.to_obj_arg());
    cnstr_set(r, 1, o2.to_obj_arg());
    cnstr_set(r, 2, o3.to_obj_arg());
    cnstr_set(r, 3, o4.to_obj_arg());
    cnstr_set(r, 4, o5.to_obj_arg());
    cnstr_set(r, 5, o6.to_obj_arg());
    cnstr_set(r, 6, o7.to_obj_arg());
    return object_ref(r);
}

/* The following definition is a low level hack that relies on the fact that sizeof(object_ref) == sizeof(object *). */
inline object_ref const & cnstr_get_ref(object * o, unsigned i) {
    static_assert(sizeof(object_ref) == sizeof(object *), "unexpected object_ref size"); // NOLINT
    lean_assert(is_cnstr(o));
    lean_assert(i < lean_ctor_num_objs(o));
    return reinterpret_cast<object_ref const *>(lean_to_ctor(o)->m_objs)[i];
}

inline object_ref const & cnstr_get_ref(object_ref const & ref, unsigned i) {
    return cnstr_get_ref(ref.raw(), i);
}

template<class T>
inline T const & cnstr_get_ref_t(object_ref const & o, unsigned i) {
    static_assert(sizeof(T) == sizeof(object_ref), "unexpected object wrapper size");
    return static_cast<T const &>(cnstr_get_ref(o.raw(), i));
}


/* Given `T` which is a subclass of object_ref that wraps a Lean value of type `Ty`,
   convert a value `o` of `Option Ty` into `optional<T>` */
template<typename T> optional<T> to_optional(obj_arg o) {
    if (is_scalar(o)) return optional<T>();
    T r(cnstr_get(o, 0), true);
    dec(o);
    return optional<T>(r);
}

/* "Borrow" version of `to_optional` */
template<typename T> optional<T> to_optional(b_obj_arg o, bool) {
    if (is_scalar(o)) return optional<T>();
    T r(cnstr_get(o, 0), true);
    return optional<T>(r);
}

/* Given `T` which is a scalar type that wraps a Lean scalar value of type `Ty`,
   convert a value `o` of `Option Ty` into `optional<T>` */
template<typename T> optional<T> to_optional_scalar(obj_arg o) {
    if (is_scalar(o)) return optional<T>();
    T r = static_cast<T>(unbox(cnstr_get(o, 0)));
    dec(o);
    return optional<T>(r);
}

template<typename T> obj_res to_object(optional<T> const & o) {
    if (o) {
        obj_res r = alloc_cnstr(1, 1, 0);
        cnstr_set(r, 0, o->to_obj_arg());
        return r;
    } else {
        return box(0);
    }
}

/*
inductive Except (ε : Type u) (α : Type v)
| error {} : ε → Except
| ok {} : α → Except
*/

template<typename T> object * mk_except_ok(T const & val) {
    obj_res r = alloc_cnstr(1, 1, 0);
    cnstr_set(r, 0, val.to_obj_arg());
    return r;
}

template<typename T> object * mk_except_error(T const & err) {
    obj_res r = alloc_cnstr(0, 1, 0);
    cnstr_set(r, 0, err.to_obj_arg());
    return r;
}

inline object * mk_except_error_string(char const * err) {
    obj_res r = alloc_cnstr(0, 1, 0);
    cnstr_set(r, 0, mk_string(err));
    return r;
}

/* Given `o` representing a Lean value of type `Except String A`, return `T` an smart pointer
   that encapsulates `A` values or throw an exception */
template<typename T> T get_except_value(obj_arg o) {
    if (cnstr_tag(o) == 1) {
        T result(cnstr_get(o, 0), true);
        dec(o);
        return result;
    } else {
        std::string err = string_to_std(cnstr_get(o, 0));
        dec(o);
        throw exception(err);
    }
}

// Remark: `T` must be an `object_ref`.
#define TO_REF(T, o) reinterpret_cast<T const &>(o)
}
