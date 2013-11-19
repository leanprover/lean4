/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <functional>
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
   \brief Copy the cells in the list \c l to the buffer \c r.
*/
template<typename T>
void to_buffer(list<T> const & l, buffer<typename list<T>::cell *> & r) {
    typename list<T>::cell * it = l.raw();
    while (it) {
        r.push_back(it);
        it = it->tail().raw();
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
    static_assert(std::is_same<typename std::result_of<F(T const &)>::type, T>::value,
                  "map: return type of f is not sxpr");
    if (is_nil(l)) {
        return l;
    } else {
        buffer<typename list<T>::cell*> tmp;
        to_buffer(l, tmp);
        unsigned i = tmp.size();
        list<T> r;
        while (i > 0) {
            --i;
            r = cons(f(tmp[i]->head()), r);
        }
        return l;
    }
}

/**
   \brief Semantically equivalent to \c map, but it tries to reuse
   list cells. The elements are compared using the predicate \c eq.
*/
template<typename T, typename F, typename Eq = std::equal_to<T>>
list<T> map_reuse(list<T> const & l, F f, Eq const & eq = Eq()) {
    if (is_nil(l)) {
        return l;
    } else {
        typedef typename list<T>::cell cell;
        buffer<std::pair<T, cell*>> tmp;
        cell * it = l.raw();
        while (it) {
            tmp.emplace_back(f(it->head()), it);
            it = it->tail().raw();
        }
        unsigned i = tmp.size();
        lean_assert(i > 0);
        while (i > 0) {
            --i;
            std::pair<T, cell*> const & p = tmp[i];
            if (!eq(p.first, p.second->head())) {
                list<T> r(p.first, p.second->tail());
                while (i > 0) {
                    --i;
                    std::pair<T, cell*> const & p = tmp[i];
                    r = cons(p.first, r);
                }
                return r;
            }
        }
        return l;
    }
}

/**
   \brief Given list <tt>(a_0, ..., a_k)</tt>, exec f(a_0); f(a_1); ... f(a_k)</tt>.
*/
template<typename T, typename F>
void for_each(list<T> const & l, F f) {
    static_assert(std::is_same<typename std::result_of<F(T const &)>::type, void>::value,
                  "for_each: return type of f is not void");
    typedef typename list<T>::cell cell;
    cell * it = l.raw();
    while (it) {
        f(it->head());
        it = it->tail().raw();
    }
}

/**
   \brief Compare two lists using the binary predicate p.
*/
template<typename T, typename P>
bool compare(list<T> const & l1, list<T> const & l2, P p) {
    static_assert(std::is_same<typename std::result_of<P(T const &, T const &)>::type, bool>::value,
                  "compare: return type of f is not bool");
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
