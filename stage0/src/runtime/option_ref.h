/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "runtime/object_ref.h"

namespace lean {
/* Wrapper for manipulating Lean option values in C++ */
template<typename T>
class option_ref : public object_ref {
public:
    explicit option_ref(obj_arg o):object_ref(o) {}
    option_ref(b_obj_arg o, bool b):object_ref(o, b) {}
    option_ref():object_ref(box(0)) {}
    option_ref(option_ref const & other):object_ref(other) {}
    option_ref(option_ref && other):object_ref(std::move(other)) {}
    explicit option_ref(T const & a):object_ref(mk_cnstr(1, a.raw())) { inc(a.raw()); }
    explicit option_ref(T const * a) { if (a) *this = option_ref(*a); }
    explicit option_ref(option_ref<T> const * o) { if (o) *this = *o; }
    explicit option_ref(optional<T> const & o):option_ref(o ? &*o : nullptr) {}

    option_ref & operator=(option_ref const & other) { object_ref::operator=(other); return *this; }
    option_ref & operator=(option_ref && other) { object_ref::operator=(std::move(other)); return *this; }

    explicit operator bool() const { return !is_scalar(raw()); }
    optional<T> get() const { return *this ? some(static_cast<T const &>(cnstr_get_ref(*this, 0))) : optional<T>(); }

    T get_val() const { lean_assert(*this); return static_cast<T const &>(cnstr_get_ref(*this, 0)); }

    /** \brief Structural equality. */
    friend bool operator==(option_ref const & o1, option_ref const & o2) {
        return o1.get() == o2.get();
    }
    friend bool operator!=(option_ref const & o1, option_ref const & o2) { return !(o1 == o2); }

    /*
    // lexicographical order
    friend bool operator<(option_ref const & l1, option_ref const & l2) {
        object * it1 = l1.raw();
        object * it2 = l2.raw();
        while (!is_scalar(it1) && !is_scalar(it2)) {
            if (it1 == it2)
                return false;
            T const & h1 = ::lean::head<T>(it1);
            T const & h2 = ::lean::head<T>(it2);
            if (h1 < h2)
                return true;
            if (h2 < h1)
                return false;
            it1 = cnstr_obj(it1, 1);
            it2 = cnstr_obj(it2, 1);
        }
        return is_scalar(it1) && !is_scalar(it2);
    }
     */
};
}
