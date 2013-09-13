/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/free_vars.h"
#include "kernel/expr_sets.h"
#include "kernel/replace.h"
#include "kernel/metavar.h"

namespace lean {
/**
    \brief Functional object for checking whether a kernel expression has free variables or not.

    \remark We assume that a metavariable contains free variables.
    This is an approximation, since we don't know how the metavariable will be instantiated.
*/
class has_free_vars_fn {
protected:
    expr_cell_offset_set m_cached;

    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            return false;
        case expr_kind::MetaVar:
            return true;
        case expr_kind::Var:
            return var_idx(e) >= offset;
        case expr_kind::App: case expr_kind::Eq: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Let:
            break;
        }

        if (e.raw()->is_closed())
            return false;

        if (offset == 0) {
            return apply_core(e, 0);
        } else {
            // The apply_core(e, 0) may seem redundant, but it allows us to
            // mark nested closed expressions.
            return apply_core(e, 0) && apply_core(e, offset);
        }
    }

    bool apply_core(expr const & e, unsigned offset) {
        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            expr_cell_offset p(e.raw(), offset);
            if (m_cached.find(p) != m_cached.end())
                return false;
        }

        bool result = false;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value: case expr_kind::Var: case expr_kind::MetaVar:
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
            result = (let_type(e) && apply(let_type(e), offset)) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
            break;
        }

        if (!result) {
            if (offset == 0)
                e.raw()->set_closed();
            if (shared)
                m_cached.insert(expr_cell_offset(e.raw(), offset));
        }

        return result;
    }
public:
    has_free_vars_fn() {}
    bool operator()(expr const & e) { return apply(e, 0); }
};

bool has_free_vars(expr const & e) {
    return has_free_vars_fn()(e);
}

/**
    \brief Functional object for checking whether a kernel expression has a free variable in the range <tt>[low, high)</tt> or not.

    \remark We assume that a metavariable contains free variables.
    This is an approximation, since we don't know how the metavariable will be instantiated.
*/
class has_free_var_in_range_fn {
protected:
    unsigned             m_low;
    unsigned             m_high;
    expr_cell_offset_set m_cached;

    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            return false;
        case expr_kind::MetaVar:
            return true;
        case expr_kind::Var:
            return var_idx(e) >= offset + m_low && var_idx(e) < offset + m_high;
        case expr_kind::App: case expr_kind::Eq: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Let:
            break;
        }

        if (e.raw()->is_closed())
            return false;

        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            expr_cell_offset p(e.raw(), offset);
            if (m_cached.find(p) != m_cached.end())
                return false;
        }

        bool result = false;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value: case expr_kind::Var: case expr_kind::MetaVar:
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
            result = (let_type(e) && apply(let_type(e), offset)) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
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

bool has_free_var(expr const & e, unsigned vidx) {
    return has_free_var_in_range_fn(vidx, vidx+1)(e);
}

bool has_free_var(expr const & e, unsigned low, unsigned high) {
    return has_free_var_in_range_fn(low, high)(e);
}

expr lower_free_vars(expr const & e, unsigned s, unsigned d) {
    lean_assert(d > 0);
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= s + offset) {
            lean_assert(var_idx(e) >= offset + d);
            return mk_var(var_idx(e) - d);
        } else if (is_metavar(e)) {
            return add_lower(e, s + offset, d);
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}

expr lift_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0)
        return e;
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e) && var_idx(e) >= s + offset) {
            return mk_var(var_idx(e) + d);
        } else if (is_metavar(e)) {
            return add_lift(e, s + offset, d);
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}
}
