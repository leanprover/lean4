/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include "kernel/expr.h"

namespace lean {
/* pair (expression, unsigned int) with cached hash code */
struct expr_unsigned {
    expr         m_expr;
    unsigned     m_nargs;
    unsigned     m_hash;
    expr_unsigned(expr const & fn, unsigned nargs):
        m_expr(fn), m_nargs(nargs), m_hash(hash(hash(m_expr), m_nargs)) {}
};

struct expr_unsigned_hash_fn {
    unsigned operator()(expr_unsigned const & k) const { return k.m_hash; }
};

struct expr_unsigned_eq_fn {
    bool operator()(expr_unsigned const & k1, expr_unsigned const & k2) const {
        return k1.m_expr == k2.m_expr && k1.m_nargs == k2.m_nargs;
    }
};

/* mapping from (expr, unsigned) -> T */
template<typename T>
using expr_unsigned_map = typename std::unordered_map<expr_unsigned, T, expr_unsigned_hash_fn, expr_unsigned_eq_fn>;
}
