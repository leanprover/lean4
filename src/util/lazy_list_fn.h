/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/lazy_list.h"
#include "util/list.h"

namespace lean {
template<typename T>
lazy_list<T> take(unsigned sz, lazy_list<T> l) {
    if (sz == 0 || !l) {
        return lazy_list<T>();
    } else {
        return lazy_list<T>(head(l), [=]() { return take(sz - 1, tail(l)); });
    }
}

template<typename T1, typename T2>
lazy_list<std::pair<T1, T2>> zip(lazy_list<T1> const & l1, lazy_list<T2> const & l2) {
    if (l1 && l2) {
        return lazy_list<std::pair<T1, T2>>(mk_pair(head(l1), head(l2)), [=]() { return zip(tail(l1), tail(l2)); });
    } else {
        return lazy_list<std::pair<T1, T2>>();
    }
}

template<typename T>
lazy_list<T> to_lazy(list<T> const & l) {
    if (l)
        return lazy_list<T>(head(l), [=]() { return to_lazy(tail(l)); });
    else
        return lazy_list<T>();
}

template<typename T>
lazy_list<T> append(lazy_list<T> const & l1, lazy_list<T> const & l2) {
    if (!l1)
        return l2;
    else if (!l2)
        return l1;
    else
        return lazy_list<T>(head(l1), [=]() { return append(tail(l1), l2); });
}

template<typename T, typename F>
lazy_list<T> map(lazy_list<T> const & l, F && f) {
    if (!l)
        return l;
    else
        return lazy_list<T>(f(head(l)), [=]() { return map(tail(l), f); });
}

template<typename T>
lazy_list<T> interleave(lazy_list<T> const & l1, lazy_list<T> const & l2) {
    if (!l1)
        return l2;
    else if (!l2)
        return l1;
    else
        return lazy_list<T>(head(l1), [=]() { return interleave(l2, tail(l1)); });
}

template<typename T, typename P>
lazy_list<T> filter(lazy_list<T> const & l, P && p) {
    if (!l)
        return l;
    else if (p(head(l)))
        return lazy_list<T>(head(l), [=]() { return filter(tail(l), p); });
    else
        return filter(tail(l), p);
}

template<typename T, typename F>
lazy_list<T> map_append_aux(lazy_list<T> const & h, lazy_list<T> const & l, F && f) {
    if (!l)
        return h;
    else if (h)
        return lazy_list<T>(head(h), [=]() { return map_append_aux(tail(h), l, f); });
    else
        return map_append_aux(f(head(l)), tail(l), f);
}

template<typename T, typename F>
lazy_list<T> map_append(lazy_list<T> const & l, F && f) {
    return map_append_aux(lazy_list<T>(), l, f);
}
}
