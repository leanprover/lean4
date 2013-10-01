/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/list.h"
#include "util/buffer.h"
#include "util/pair.h"

namespace lean {
/**
   \brief Copy the values in the list \c l to the buffer \c r.
*/
template<typename T>
void to_buffer(list<T> const & l, buffer<T> & r) {
    for (T const & v : l) {
        r.push_back(v);
    }
}

/**
    \brief Auxiliary function for reverse function.
*/
template<typename T>
list<T> reverse_aux(list<T> const & l, list<T> const & r) {
    if (is_nil(l))
        return r;
    else
        return reverse_aux(cdr(l), cons(car(l), r));
}

/**
   \brief Return the reverse list.
*/
template<typename T>
list<T> reverse(list<T> const & l) {
    return reverse_aux(l, list<T>());
}

/**
   \brief Return two lists \c l1 and \c l2 of approximately the same size s.t.
   <tt>append(l1, l2) == l</tt>
*/
template<typename T>
std::pair<list<T>, list<T>> split(list<T> const & l) {
    if (is_nil(l)) {
        return mk_pair(l, l);
    } else if (is_nil(cdr(l))) {
        return mk_pair(l, list<T>());
    } else {
        buffer<T> tmp;
        to_buffer(l, tmp);
        unsigned mid = tmp.size() / 2;
        auto beg = tmp.begin();
        lean_assert(beg + mid <= tmp.end());
        return mk_pair(to_list(beg, beg + mid),
                       to_list(beg + mid, tmp.end()));
    }
}

/**
   \brief Return two lists \c l1 and \c l2 of approximately the same size s.t.
   <tt>append(l1, reverse(l2)) == l</tt>
*/
template<typename T>
std::pair<list<T>, list<T>> split_reverse_second(list<T> const & l) {
    if (is_nil(l)) {
        return mk_pair(l, l);
    } else if (is_nil(cdr(l))) {
        return mk_pair(l, list<T>());
    } else {
        buffer<T> tmp;
        to_buffer(l, tmp);
        unsigned mid = tmp.size() / 2;
        auto beg = tmp.begin();
        lean_assert(beg + mid <= tmp.end());
        return mk_pair(to_list(beg, beg + mid), reverse_to_list(beg+mid, tmp.end()));
    }
}

/**
   \brief Append two lists
*/
template<typename T>
list<T> append(list<T> const & l1, list<T> const & l2) {
    if (!l1) {
        return l2;
    } else if (!l2) {
        return l1;
    } else {
        buffer<T> tmp;
        list<T> r = l2;
        to_buffer(l1, tmp);
        unsigned i = tmp.size();
        while (i > 0) {
            --i;
            r = cons(tmp[i], r);
        }
        return r;
    }
}

/**
   \brief Given list <tt>(a_0, ..., a_k)</tt>, return list <tt>(f(a_0), ..., f(a_k))</tt>.
*/
template<typename T, typename F>
list<T> map(list<T> const & l, F f) {
    if (is_nil(l)) {
        return l;
    } else {
        return list<T>(f(head(l)), map(tail(l), f));
    }
}

/**
   \brief Given list <tt>(a_0, ..., a_k)</tt>, exec f(a_0); f(a_1); ... f(a_k)</tt>.
*/
template<typename T, typename F>
void for_each(list<T> const & l, F f) {
    if (is_nil(l)) {
        return;
    } else {
        f(head(l));
        return for_each(tail(l), f);
    }
}

/**
   \brief Compare two lists using the binary predicate p.
*/
template<typename T, typename P>
bool compare(list<T> const & l1, list<T> const & l2, P p) {
    auto it1 = l1.begin();
    auto it2 = l2.begin();
    auto end1 = l1.end();
    auto end2 = l2.end();
    for (; it1 != end1 && it2 != end2; ++it1, ++it2) {
        if (!p(*it1, *it2))
            return false;
    }
    return it1 == end1 && it2 == end2;
}
}
