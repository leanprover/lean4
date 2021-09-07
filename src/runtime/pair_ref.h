/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/object_ref.h"

namespace lean {
/* Wrapper for manipulating Lean pairs in C++ */
template<typename T1, typename T2>
class pair_ref : public object_ref {
public:
    explicit pair_ref(b_obj_arg o):object_ref(o) {}
    explicit pair_ref(b_obj_arg o, bool b):object_ref(o, b) {}
    pair_ref(T1 const & a, T2 const & b):object_ref(mk_cnstr(0, a.raw(), b.raw())) { inc(a.raw()); inc(b.raw()); }
    pair_ref(pair_ref const & other):object_ref(other) {}
    pair_ref(pair_ref && other):object_ref(other) {}
    pair_ref & operator=(pair_ref const & other) { object_ref::operator=(other); return *this; }
    pair_ref & operator=(pair_ref && other) { object_ref::operator=(other); return *this; }

    T1 const & fst() const { return static_cast<T1 const &>(cnstr_get_ref(*this, 0)); }
    T2 const & snd() const { return static_cast<T2 const &>(cnstr_get_ref(*this, 1)); }
};

template<typename T1, typename T2> bool operator==(pair_ref<T1, T2> const & a, pair_ref<T1, T2> const & b) {
    return a.fst() == b.fst() && a.snd() == b.snd();
}

template<typename T1, typename T2> bool operator!=(pair_ref<T1, T2> const & a, pair_ref<T1, T2> const & b) {
    return !(a == b);
}

template<typename T1, typename T2> bool operator<(pair_ref<T1, T2> const & a, pair_ref<T1, T2> const & b) {
    if (a.fst() != b.fst()) return a.fst() < b.fst();
    else return a.snd() < b.snd();
}
}
