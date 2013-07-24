/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "sexpr.h"
#include "debug.h"

namespace lean {

template<typename F>
void foreach(sexpr const & l, F f) {
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
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return l;
    }
    else {
        lean_assert(is_cons(l));
        return sexpr(f(head(l)), map(tail(l), f));
    }
}

template<typename P>
sexpr filter(sexpr const & l, P p) {
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return l;
    }
    else {
        lean_assert(is_cons(l));
        if (p(head(l)))
            return sexpr(head(l), filter(tail(l), p));
        else
            return filter(tail(l), p);
    }
}

template<typename P>
bool contains(sexpr const & l, P p) {
    lean_assert(is_list(l));
    if (is_nil(l)) {
        return false;
    }
    else {
        lean_assert(is_cons(l));
        return p(head(l)) || contains(tail(l), p);
    }
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

sexpr append(sexpr const & l1, sexpr const & l2);

sexpr reverse(sexpr const & l);

}
