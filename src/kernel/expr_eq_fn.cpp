/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_eq_fn.h"

#ifndef LEAN_EQ_CACHE_THRESHOLD
#define LEAN_EQ_CACHE_THRESHOLD 4
#endif

namespace lean {
bool expr_eq_fn::apply(expr const & a, expr const & b) {
    if (is_eqp(a, b))          return true;
    if (a.hash() != b.hash())  return false;
    if (a.kind() != b.kind())  return false;
    if (is_var(a))             return var_idx(a) == var_idx(b);
    if (m_counter >= LEAN_EQ_CACHE_THRESHOLD && is_shared(a) && is_shared(b)) {
        auto p = std::make_pair(a.raw(), b.raw());
        if (!m_eq_visited)
            m_eq_visited.reset(new expr_cell_pair_set);
        if (m_eq_visited->find(p) != m_eq_visited->end())
            return true;
        m_eq_visited->insert(p);
    }
    check_system("expression equality test");
    switch (a.kind()) {
    case expr_kind::Var:
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::Constant:
        return
            const_name(a) == const_name(b) &&
            compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
    case expr_kind::Meta:
        return
            mlocal_name(a) == mlocal_name(b) &&
            apply(mlocal_type(a), mlocal_type(b));
    case expr_kind::Local:
        return
            mlocal_name(a) == mlocal_name(b) &&
            apply(mlocal_type(a), mlocal_type(b)) &&
            (!m_compare_binder_info || local_pp_name(a) == local_pp_name(b));
            (!m_compare_binder_info || local_info(a) == local_info(b));
    case expr_kind::App:
        m_counter++;
        return
            apply(app_fn(a), app_fn(b)) &&
            apply(app_arg(a), app_arg(b));
    case expr_kind::Lambda: case expr_kind::Pi:
        m_counter++;
        return
            apply(binding_domain(a), binding_domain(b)) &&
            apply(binding_body(a), binding_body(b)) &&
            (!m_compare_binder_info || binding_info(a) == binding_info(b));
    case expr_kind::Sort:
        return sort_level(a) == sort_level(b);
    case expr_kind::Macro:
        m_counter++;
        if (macro_def(a) != macro_def(b) || macro_num_args(a) != macro_num_args(b))
            return false;
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (!apply(macro_arg(a, i), macro_arg(b, i)))
                return false;
        }
        return true;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}
