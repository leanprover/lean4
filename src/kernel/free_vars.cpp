/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "free_vars.h"
#include "sets.h"
#include "replace.h"

namespace lean {

/** \brief Functional object for checking whether a kernel expression has free variables or not. */
class has_free_vars_fn {
protected:
    expr_cell_offset_set m_visited;
    bool                 m_set_closed_flag;

    virtual bool process_var(expr const & x, unsigned offset) {
        return var_idx(x) >= offset;
    }

    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            return false;
        case expr_kind::Var:
            return process_var(e, offset);
        case expr_kind::App: case expr_kind::Eq: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Let:
            break;
        }

        if (e.raw()->is_closed())
            return false;

        if (is_shared(e)) {
            expr_cell_offset p(e.raw(), offset);
            if (m_visited.find(p) != m_visited.end())
                return false;
            m_visited.insert(p);
        }

        bool result = false;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value: case expr_kind::Var:
            // easy cases were already handled
            lean_unreachable(); return false;
        case expr_kind::App:
            result = std::any_of(begin_args(e), end_args(e), [=](expr const & arg){ return apply(arg, offset); });
            break;
        case expr_kind::Eq:
            result = apply(eq_lhs(e), offset) || apply(eq_rhs(e), offset);
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            result = apply(abst_domain(e), offset) || apply(abst_body(e), offset + 1);
            break;
        case expr_kind::Let:
            result = apply(let_value(e), offset) || apply(let_body(e), offset + 1);
            break;
        }

        if (m_set_closed_flag && !result)
            e.raw()->set_closed();

        return result;
    }
public:
    has_free_vars_fn(bool s):m_set_closed_flag(s) {}
    bool operator()(expr const & e) { return apply(e, 0); }
};

bool has_free_vars(expr const & e) {
    return has_free_vars_fn(true)(e);
}

/** \brief Functional object for checking whether a kernel expression has a free variable in the range <tt>[low, high)</tt> or not. */
class has_free_var_in_range_fn : public has_free_vars_fn {
    unsigned m_low;
    unsigned m_high;
    virtual bool process_var(expr const & x, unsigned offset) {
        return var_idx(x) >= offset + m_low && var_idx(x) < offset + m_high;
    }
public:
    has_free_var_in_range_fn(unsigned low, unsigned high):
        has_free_vars_fn(false /* We should not set the closed flag since we are only considering a range of free variables */),
        m_low(low),
        m_high(high) {
        lean_assert(low < high);
    }
};

bool has_free_var(expr const & e, unsigned vidx) {
    return has_free_var_in_range_fn(vidx, vidx+1)(e);
}

bool has_free_var(expr const & e, unsigned low, unsigned high) {
    return has_free_var_in_range_fn(low, high)(e);
}

expr lower_free_vars(expr const & e, unsigned d) {
    lean_assert(d > 0);
    lean_assert(!has_free_var(e, 0, d));
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= offset) {
            lean_assert(var_idx(e) >= offset + d);
            return var(var_idx(e) - d);
        }
        else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}

expr lift_free_vars(expr const & e, unsigned d) {
    if (d == 0)
        return e;
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= offset) {
            return var(var_idx(e) + d);
        }
        else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}

}
