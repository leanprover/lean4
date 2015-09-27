/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/sexpr.h"
#include "util/debug.h"

namespace lean {

template<typename F>
void for_each(sexpr const & l, F f) {
    static_assert(std::is_same<typename std::result_of<F(sexpr const &)>::type, void>::value,
                  "foreach: return type of f is not void");
    lean_assert(is_list(l));
    sexpr const * h = &l;
    while (!is_nil(*h)) {
        lean_assert(is_cons(*h));
        f(head(*h));
        h = &tail(*h);
    }
}

template<typename F>
sexpr map(sexpr const & l, F f) {
    static_assert(std::is_same<typename std::result_of<F(sexpr const &)>::type, sexpr>::value,
                  "map: return type of f is not sxpr");
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return l;
    } else {
        lean_assert(is_cons(l));
        auto x = f(head(l)); // force left-to-right evaluation order
        return sexpr(x, map(tail(l), f));
    }
}

template<typename P>
sexpr filter(sexpr const & l, P p) {
    static_assert(std::is_same<typename std::result_of<P(sexpr const &)>::type, bool>::value,
                  "filter: return type of p is not bool");
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return l;
    } else {
        lean_assert(is_cons(l));
        if (p(head(l)))
            return sexpr(head(l), filter(tail(l), p));
        else
            return filter(tail(l), p);
    }
}

template<class T, class BOP>
T foldl(sexpr const & l, T init, BOP op) {
    static_assert(std::is_same<typename std::result_of<BOP(T, sexpr const &)>::type, T>::value,
                  "foldl: return type of op is not T");
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return init;
    } else {
        lean_assert(is_cons(l));
        return foldl(tail(l), op(init, head(l)), op);
    }
}

template<class T, class BOP>
T foldr(sexpr const & l, T init, BOP op) {
    static_assert(std::is_same<typename std::result_of<BOP(sexpr const &, T)>::type, T>::value,
                  "foldr: return type of op is not T");
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return init;
    } else {
        lean_assert(is_cons(l));
        return op(head(l), foldr(tail(l), init, op));
    }
}

template<typename P>
bool forall(sexpr const & l, P p) {
    static_assert(std::is_same<typename std::result_of<P(sexpr const &)>::type, bool>::value,
                  "forall: return type of p is not bool");
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return true;
    } else {
        lean_assert(is_cons(l));
        return p(head(l)) && forall(tail(l), p);
    }
}

template<typename P>
bool contains(sexpr const & l, P p) {
    static_assert(std::is_same<typename std::result_of<P(sexpr const &)>::type, bool>::value,
                  "contains: return type of p is not bool");
    lean_assert(is_list(l));
    sexpr const * h = &l;
    while (!is_nil(*h)) {
        lean_assert(is_cons(*h));
        if (p(head(*h)))
            return true;
        h = &tail(*h);
    }
    return false;
}

template<typename T>
bool member(T const & e, sexpr const & l) {
    lean_assert(is_list(l));
    sexpr const * curr = &l;
    while (!is_nil(*curr)) {
        if (head(*curr) == e)
            return true;
        curr = &tail(*curr);
    }
    return false;
}

template<typename P>
sexpr const * find(sexpr const & l, P p) {
    static_assert(std::is_same<typename std::result_of<P(sexpr const &)>::type, bool>::value,
                  "find: return type of p is not bool");
    lean_assert(is_list(l));
    sexpr const * h = &l;
    while (!is_nil(*h)) {
        lean_assert(is_cons(*h));
        if (p(head(*h)))
            return &(head(*h));
        h = &tail(*h);
    }
    return nullptr;
}

sexpr append(sexpr const & l1, sexpr const & l2);

sexpr reverse(sexpr const & l);

}
