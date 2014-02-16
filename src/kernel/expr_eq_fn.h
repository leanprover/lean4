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
    std::unique_ptr<expr_cell_pair_set> m_eq_visited;
    bool apply(optional<expr> const & a0, optional<expr> const & b0);
    bool apply(expr const & a, expr const & b);
public:
    bool operator()(expr const & a, expr const & b) { return apply(a, b); }
    void clear() { m_eq_visited.reset(); }
};
}
