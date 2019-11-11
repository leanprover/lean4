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
/** \brief Copy the values in the list \c l to the buffer \c r. */
template<typename T>
void to_buffer(list<T> const & l, buffer<T> & r) {
    for (T const & v : l) {
        r.push_back(v);
    }
}

/** \brief Copy the cells in the list \c l to the buffer \c r. */
template<typename T>
void to_buffer(list<T> const & l, buffer<typename list<T>::cell *> & r) {
    typename list<T>::cell * it = l.raw();
    while (it) {
        r.push_back(it);
        it = it->tail().raw();
    }
}

/** \brief Create a list using the values in the cells from \c begin to \c end. */
template<typename T>
list<T> cells_to_list(typename list<T>::cell * const * begin, typename list<T>::cell * const * end) {
    list<T> r;
    auto it = end;
    while (it != begin) {
        --it;
        r = cons((*it)->head(), r);
    }
    return r;
}

/** \brief Create a list using the values in the cells from \c b. */
template<typename T>
list<T> buffer_to_list(buffer<typename list<T>::cell*> const & b) {
    return cells_to_list<T>(b.begin(), b.end());
}

/** \brief Return the reverse list. */
template<typename T>
list<T> reverse(list<T> const & l) {
    if (is_nil(l)) {
        return l;
    } else {
        buffer<typename list<T>::cell *> tmp;
        to_buffer(l, tmp);
        std::reverse(tmp.begin(), tmp.end());
        return buffer_to_list<T>(tmp);
    }
}

/**
   \brief Return two lists \c l1 and \c l2 of approximately the same size s.t.
   <tt>append(l1, l2) == l</tt>
*/
template<typename T>
pair<list<T>, list<T>> split(list<T> const & l) {
    if (is_nil(l)) {
        return mk_pair(l, l);
    } else if (is_nil(cdr(l))) {
        return mk_pair(l, list<T>());
    } else {
        buffer<typename list<T>::cell*> tmp;
        to_buffer(l, tmp);
        unsigned mid = tmp.size() / 2;
        auto beg = tmp.begin();
        lean_assert(beg + mid <= tmp.end());
        return mk_pair(cells_to_list<T>(beg, beg + mid),
                       cells_to_list<T>(beg + mid, tmp.end()));
    }
}

/**
   \brief Return two lists \c l1 and \c l2 of approximately the same size s.t.
   <tt>append(l1, reverse(l2)) == l</tt>
*/
template<typename T>
pair<list<T>, list<T>> split_reverse_second(list<T> const & l) {
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

/** \brief Append two lists */
template<typename T>
list<T> append(list<T> const & l1, list<T> const & l2) {
    if (!l1) {
        return l2;
    } else if (!l2) {
        return l1;
    } else {
        buffer<typename list<T>::cell*> tmp;
        list<T> r = l2;
        to_buffer(l1, tmp);
        unsigned i = tmp.size();
        while (i > 0) {
            --i;
            r = cons(tmp[i]->head(), r);
        }
        return r;
    }
}

/** \brief Given list <tt>(a_0, ..., a_k)</tt>, return list <tt>(f(a_0), ..., f(a_k))</tt>. */
template<typename To, typename From, typename F>
list<To> map2(list<From> const & l, F && f) {
    static_assert(std::is_same<typename std::result_of<F(From const &)>::type, To>::value,
                  "map: return type of f is not equal to input type");
    if (is_nil(l)) {
        return list<To>();
    } else {
        buffer<To> new_vs;
        for (auto const & v : l)
            new_vs.push_back(f(v));
        return to_list(new_vs.begin(), new_vs.end());
    }
}

/** \brief Given list <tt>(a_0, ..., a_k)</tt>, return list <tt>(f(a_0), ..., f(a_k))</tt>. */
template<typename T, typename F>
list<T> map(list<T> const & l, F && f) {
    return map2<T, T, F>(l, std::move(f));
}

/**
   \brief Filter/Remove elements from the list
   that do not satisfy the given predicate.
*/
template<typename T, typename P>
list<T> filter(list<T> const & l, P && p) {
    if (is_nil(l)) {
        return l;
    } else {
        buffer<typename list<T>::cell*> tmp;
        to_buffer(l, tmp);
        unsigned i = tmp.size();
        while (i > 0) {
            --i;
            if (!p(tmp[i]->head())) {
                list<T> r = tmp[i]->tail();
                while (i > 0) {
                    --i;
                    if (p(tmp[i]->head()))
                        r = cons(tmp[i]->head(), r);
                }
                return r;
            }
        }
        return l; // not element was removed
    }
}

/** \brief Remove all occurrences of \c a from \c l */
template<typename T>
list<T> remove(list<T> const & l, T const & a) {
    return filter(l, [&](T const & v) { return a != v; });
}

/** \brief Remove the last element that satisfies \c p. */
template<typename T, typename P>
list<T> remove_last(list<T> const & l, P && p) {
    if (!is_nil(l)) {
        buffer<typename list<T>::cell*> tmp;
        to_buffer(l, tmp);
        unsigned i = tmp.size();
        while (i > 0) {
            --i;
            if (p(tmp[i]->head())) {
                list<T> r = tmp[i]->tail();
                while (i > 0) {
                    --i;
                    r = cons(tmp[i]->head(), r);
                }
                return r;
            }
        }
    }
    return l;
}

/**
   \brief Similar to \c map but \c f has signature

       <tt>bool f(T const & in, T & out)</tt>

   If \c out becomes part of the result iff \c f returns true.
*/
template<typename To, typename From, typename F>
list<To> map_filter(list<From> const & l, F && f) {
    if (is_nil(l)) {
        return list<To>();
    } else {
        buffer<typename list<From>::cell*> tmp;
        to_buffer(l, tmp);
        unsigned i = tmp.size();
        list<To> r;
        while (i > 0) {
            --i;
            To out;
            if (f(tmp[i]->head(), out))
                r = cons(out, r);
        }
        return r;
    }
}

template<typename T, typename F>
list<T> map_append(list<T> const & l, F && f) {
    if (is_nil(l)) {
        return l;
    } else {
        buffer<T> tmp;
        for (auto const & v : l)
            to_buffer(f(v), tmp);
        return to_list(tmp.begin(), tmp.end());
    }
}

/**
   \brief Semantically equivalent to \c map, but it tries to reuse
   list cells. The elements are compared using the predicate \c eq.
*/
template<typename T, typename F, typename Eq = std::equal_to<T>>
list<T> map_reuse(list<T> const & l, F && f, Eq const & eq = Eq()) {
    if (is_nil(l)) {
        return l;
    } else {
        buffer<typename list<T>::cell*> tmp;
        to_buffer(l, tmp);
        auto it    = tmp.end();
        auto begin = tmp.begin();
        while (it != begin) {
            --it;
            auto curr  = *it;
            auto new_v = f(curr->head());
            if (!eq(new_v, curr->head())) {
                list<T> r(new_v, curr->tail());
                while (it != begin) {
                    --it;
                    auto curr  = *it;
                    r = cons(f(curr->head()), r);
                }
                return r;
            }
        }
        return l;
    }
}

/** \brief Given list <tt>(a_0, ..., a_k)</tt>, exec f(a_0); f(a_1); ... f(a_k)</tt>. */
template<typename T, typename F>
void for_each(list<T> const & l, F && f) {
    static_assert(std::is_same<typename std::result_of<F(T const &)>::type, void>::value,
                  "for_each: return type of f is not void");
    typedef typename list<T>::cell cell;
    cell * it = l.raw();
    while (it) {
        f(it->head());
        it = it->tail().raw();
    }
}

/** \brief Given lists <tt>(a_0, ..., a_k)</tt> and <tt>(b_0, ..., b_k)</tt>,
    exec f(a_0, b_0); f(a_1, b_1); ... f(a_k, b_k)</tt>. */
template<typename T1, typename T2, typename F>
void for_each2(list<T1> const & l1, list<T2> const & l2, F && f) {
    static_assert(std::is_same<typename std::result_of<F(T1 const &, T2 const &)>::type, void>::value,
                  "for_each2: return type of f is not void");
    typedef typename list<T1>::cell cell1;
    typedef typename list<T2>::cell cell2;
    cell1 * it1 = l1.raw();
    cell2 * it2 = l2.raw();
    while (it1 && it2) {
        f(it1->head(), it2->head());
        it1 = it1->tail().raw();
        it2 = it2->tail().raw();
    }
}

/** \brief Given lists <tt>(a_0, ..., a_k)</tt>, <tt>(b_0, ..., b_k)</tt>,
    and <tt>(c_0, ..., c_k)</tt>,
    exec f(a_0, b_0, c_0); f(a_1, b_1, c_1); ... f(a_k, b_k, c_k)</tt>. */
template<typename T1, typename T2, typename T3, typename F>
void for_each3(list<T1> const & l1, list<T2> const & l2, list<T3> const & l3, F && f) {
    static_assert(std::is_same<typename std::result_of<F(T1 const &, T2 const &, T3 const &)>::type, void>::value,
                  "for_each2: return type of f is not void");
    typedef typename list<T1>::cell cell1;
    typedef typename list<T2>::cell cell2;
    typedef typename list<T3>::cell cell3;
    cell1 * it1 = l1.raw();
    cell2 * it2 = l2.raw();
    cell3 * it3 = l3.raw();
    while (it1 && it2 && it3) {
        f(it1->head(), it2->head(), it3->head());
        it1 = it1->tail().raw();
        it2 = it2->tail().raw();
        it3 = it3->tail().raw();
    }
}

/** \brief Compare two lists using the binary predicate p. */
template<typename T, typename P>
bool compare(list<T> const & l1, list<T> const & l2, P && p) {
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

/** \brief Return the i-th element of the list */
template<typename T>
T const & get_ith(list<T> const & l, unsigned idx) {
    return idx == 0 ? head(l) : get_ith(tail(l), idx - 1);
}

/** \brief Remove the i-th element of the list (starting a 0) */
template<typename T>
list<T> remove_ith(list<T> const & l, unsigned idx) {
    if (is_nil(l))
        return l;
    else
        return idx == 0 ? tail(l) : cons(head(l), remove_ith(tail(l), idx-1));
}

list<unsigned> mk_list_range(unsigned from, unsigned to);
}
