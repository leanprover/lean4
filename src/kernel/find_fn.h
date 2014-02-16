/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/for_each_fn.h"
#include "kernel/expr.h"

namespace lean {
template<typename P>
class find_fn {
    struct pred_fn {
        optional<expr> & m_result;
        P      m_p;
        pred_fn(optional<expr> & result, P const & p):m_result(result), m_p(p) {}
        bool operator()(expr const & e, unsigned) {
            if (m_result) {
                return false; // already found result, stop the search
            } else if (m_p(e)) {
                m_result = e;
                return false; // stop the search
            } else {
                return true; // continue the search
            }
        }
    };
    optional<expr>       m_result;
    for_each_fn<pred_fn> m_proc;
public:
    find_fn(P const & p):m_proc(pred_fn(m_result, p)) {}
    optional<expr> operator()(expr const & e) { m_proc(e); return m_result; }
};

/**
   \brief Return a subexpression of \c e that satisfies the predicate \c p.
*/
template<typename P>
optional<expr> find(expr const & e, P p) {
    return find_fn<P>(p)(e);
}
}
