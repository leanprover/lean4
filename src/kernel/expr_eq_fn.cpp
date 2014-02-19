/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_eq_fn.h"

namespace lean {
bool expr_eq_fn::apply(expr const & a, expr const & b) {
    check_system("expression equality test");
    if (is_eqp(a, b))          return true;
    if (a.hash() != b.hash())  return false;
    if (a.kind() != b.kind())  return false;
    if (is_var(a))             return var_idx(a) == var_idx(b);
    if (is_shared(a) && is_shared(b)) {
        auto p = std::make_pair(a.raw(), b.raw());
        if (!m_eq_visited)
            m_eq_visited.reset(new expr_cell_pair_set);
        if (m_eq_visited->find(p) != m_eq_visited->end())
            return true;
        m_eq_visited->insert(p);
    }
    switch (a.kind()) {
    case expr_kind::Var:
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::Constant:
        return
            const_name(a) == const_name(b) &&
            compare(const_level_params(a), const_level_params(b), [](level const & l1, level const & l2) { return l1 == l2; });
    case expr_kind::Local: case expr_kind::Meta:
        return
            mlocal_name(a) == mlocal_name(b) &&
            apply(mlocal_type(a), mlocal_type(b));
    case expr_kind::App:
        return
            apply(app_fn(a), app_fn(b)) &&
            apply(app_arg(a), app_arg(b));
    case expr_kind::Pair:
        return
            apply(pair_first(a), pair_first(b)) &&
            apply(pair_second(a), pair_second(b)) &&
            apply(pair_type(a), pair_type(b));
    case expr_kind::Fst: case expr_kind::Snd:
        return apply(proj_arg(a), proj_arg(b));
    case expr_kind::Sigma: case expr_kind::Lambda: case expr_kind::Pi:
        return
            apply(binder_domain(a), binder_domain(b)) &&
            apply(binder_body(a), binder_body(b));
    case expr_kind::Sort:
        return sort_level(a) == sort_level(b);
    case expr_kind::Macro:
        return to_macro(a) == to_macro(b);
    case expr_kind::Let:
        return
            apply(let_type(a), let_type(b)) &&
            apply(let_value(a), let_value(b)) &&
            apply(let_body(a), let_body(b));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}
