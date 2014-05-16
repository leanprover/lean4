/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "kernel/free_vars.h"
#include "kernel/expr_sets.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"

namespace lean {
/**
    \brief Functional object for checking whether a kernel expression has a free variable in the range <tt>[low, high)</tt> or not.
*/
class has_free_var_in_range_fn {
protected:
    unsigned                           m_low;
    unsigned                           m_high;
    expr_cell_offset_set               m_cached;

    bool apply(expr const & e, unsigned offset) {
        unsigned range = get_free_var_range(e);
        if (range == 0) {
            lean_assert(closed(e));
            return false;
        }
        unsigned low1 = m_low + offset;
        if (low1 < m_low)
            return false; // overflow, vidx can't be >= max unsigned
        if (range <= low1) {
            return false;
        } else {
            lean_assert(range > low1);
            unsigned high1 = m_high + offset;
            if (high1 < m_high)
                return true; // overflow, vidx is always < max unsigned
            if (range <= high1)
                return true;
            // At this point, e contains a free variables in the range [0, range),
            // and it definitely contains Var(range-1).
            // Moreover [low1, high1) is a proper subset of [0, range), i.e., range > high1
            if (is_var(e))
                return var_idx(e) < high1;
        }

        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            expr_cell_offset p(e.raw(), offset);
            if (m_cached.find(p) != m_cached.end())
                return false;
        }

        bool result = false;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Sort:
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Meta:   case expr_kind::Local:
            result = apply(mlocal_type(e), offset);
            break;
        case expr_kind::App:
            result = apply(app_fn(e), offset) || apply(app_arg(e), offset);
            break;
        case expr_kind::Lambda: case expr_kind::Pi:
            result = apply(binding_domain(e), offset) || apply(binding_body(e), offset + 1);
            break;
        case expr_kind::Let:
            result = apply(let_type(e), offset) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
            break;
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(e); i++) {
                if (apply(macro_arg(e, i), offset)) {
                    result = true;
                    break;
                }
            }
            break;
        }

        if (!result && shared) {
            m_cached.insert(expr_cell_offset(e.raw(), offset));
        }
        return result;
    }
public:
    has_free_var_in_range_fn(unsigned low, unsigned high):
        m_low(low),
        m_high(high) {
        lean_assert(low < high);
    }
    bool operator()(expr const & e) { return apply(e, 0); }
};

bool has_free_var(expr const & e, unsigned low, unsigned high) {
    unsigned range = get_free_var_range(e);
    if (high <= low || range <= low)
        return false;
    if (range <= high)
        return true;
    return has_free_var_in_range_fn(low, high)(e);
}
bool has_free_var(expr const & e, unsigned i) { return has_free_var(e, i, i+1); }

expr lower_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_free_var_range(e))
        return e;
    lean_assert(s >= d);
    lean_assert(!has_free_var(e, s-d, s));
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_free_var_range(e))
                return some_expr(e); // expression e does not contain free variables with idx >= s1
            if (is_var(e) && var_idx(e) >= s1) {
                lean_assert(var_idx(e) >= offset + d);
                return some_expr(mk_var(var_idx(e) - d));
            } else {
                return none_expr();
            }
        });
}
expr lower_free_vars(expr const & e, unsigned d) { return lower_free_vars(e, d, d); }

expr lift_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_free_var_range(e))
        return e;
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_free_var_range(e))
                return some_expr(e); // expression e does not contain free variables with idx >= s1
            if (is_var(e) && var_idx(e) >= s + offset) {
                unsigned new_idx = var_idx(e) + d;
                if (new_idx < var_idx(e))
                    throw exception("invalid lift_free_vars operation, index overflow");
                return some_expr(mk_var(new_idx));
            } else {
                return none_expr();
            }
        });
}
expr lift_free_vars(expr const & e, unsigned d) { return lift_free_vars(e, 0, d); }
}
