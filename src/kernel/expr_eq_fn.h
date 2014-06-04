/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "util/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {
/**
   \brief Functional object for comparing expressions.
*/
class expr_eq_fn {
    bool m_compare_binder_info;
    // We only use the cache m_eq_visited when m_counter > LEAN_EQ_CACHE_THRESHOLD.
    // The idea is that most queries fail quickly, and it is a wast of time
    // to create the cache.
    unsigned m_counter;
    std::unique_ptr<expr_cell_pair_set> m_eq_visited;
    bool apply(expr const & a, expr const & b);
public:
    /** \brief If \c is true, then functional object will also compare binder information attached to lambda and Pi expressions */
    expr_eq_fn(bool c = false):m_compare_binder_info(c), m_counter(0) {}
    bool operator()(expr const & a, expr const & b) { m_counter = 0; return apply(a, b); }
    void clear() { m_eq_visited.reset(); }
};
}
