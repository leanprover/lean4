/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "list.h"
#include "buffer.h"
#include "pair.h"

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
   \brief Append two lists
*/
template<typename T>
list<T> append(list<T> const & l1, list<T> const & l2) {
    buffer<T> tmp;
    to_buffer(l1, tmp);
    to_buffer(l2, tmp);
    return to_list(tmp.begin(), tmp.end());
}
}
