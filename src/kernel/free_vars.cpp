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
        case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Macro:
            return false;
        case expr_kind::Var:
            return var_idx(e) >= offset;
        case expr_kind::App:    case expr_kind::Let:
        case expr_kind::Meta:   case expr_kind::Local:
        case expr_kind::Lambda: case expr_kind::Pi:  case expr_kind::Sigma:
        case expr_kind::Pair:   case expr_kind::Fst: case expr_kind::Snd:
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
        case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Macro:
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Meta:   case expr_kind::Local:
            result = apply(mlocal_type(e), offset);
        case expr_kind::App:
            result = apply(app_fn(e), offset) || apply(app_arg(e), offset);
            break;
        case expr_kind::Fst: case expr_kind::Snd:
            result = apply(proj_arg(e), offset);
            break;
        case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
            result = apply(binder_domain(e), offset) || apply(binder_body(e), offset + 1);
            break;
        case expr_kind::Let:
            result = apply(let_type(e), offset) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
            break;
        case expr_kind::Pair:
            result = apply(pair_first(e), offset) || apply(pair_second(e), offset) || apply(pair_type(e), offset);
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
   \brief Functional object for computing the range [0, R) of free variables occurring
   in an expression.
*/
class free_var_range_fn {
    expr_map<unsigned>  m_cached;

    static unsigned dec(unsigned s) { return (s == 0) ? 0 : s - 1; }

    unsigned apply(expr const & e) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Macro:
            return 0;
        case expr_kind::Var:
            return var_idx(e) + 1;
        case expr_kind::App:    case expr_kind::Let:
        case expr_kind::Meta:   case expr_kind::Local:
        case expr_kind::Lambda: case expr_kind::Pi:  case expr_kind::Sigma:
        case expr_kind::Pair:   case expr_kind::Fst: case expr_kind::Snd:
            break;
        }

        if (e.raw()->is_closed())
            return 0;

        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            auto it = m_cached.find(e);
            if (it != m_cached.end())
                return it->second;
        }

        unsigned result = 0;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Macro:
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Meta: case expr_kind::Local:
            result = apply(mlocal_type(e));
        case expr_kind::App:
            result = std::max(apply(app_fn(e)), apply(app_arg(e)));
            break;
        case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
            result = std::max(apply(binder_domain(e)), dec(apply(binder_body(e))));
            break;
        case expr_kind::Let:
            result = std::max({apply(let_type(e)), apply(let_value(e)), dec(apply(let_body(e)))});
            break;
        case expr_kind::Fst: case expr_kind::Snd:
            result = apply(proj_arg(e));
            break;
        case expr_kind::Pair:
            result = std::max({apply(pair_first(e)), apply(pair_second(e)), apply(pair_type(e))});
            break;
        }

        if (shared)
            m_cached.insert(mk_pair(e, result));

        return result;
    }
public:
    free_var_range_fn() {}
    unsigned operator()(expr const & e) { return apply(e); }
};

unsigned free_var_range(expr const & e) {
    return free_var_range_fn()(e);
}

/**
    \brief Functional object for checking whether a kernel expression has a free variable in the range <tt>[low, high)</tt> or not.
*/
class has_free_var_in_range_fn {
protected:
    unsigned                           m_low;
    unsigned                           m_high;
    expr_cell_offset_set               m_cached;
    std::unique_ptr<free_var_range_fn> m_range_fn;

    // Return true iff  m_low + offset <= vidx
    bool ge_lower(unsigned vidx, unsigned offset) const {
        unsigned low1 = m_low + offset;
        if (low1 < m_low)
            return false; // overflow, vidx can't be >= max unsigned
        return vidx >= low1;
    }

    // Return true iff vidx < m_high + offset
    bool lt_upper(unsigned vidx, unsigned offset) const {
        unsigned high1 = m_high + offset;
        if (high1 < m_high)
            return true;  // overflow, vidx is always < max unsigned
        return vidx < high1;
    }

    // Return true iff   m_low + offset <= vidx < m_high + offset
    bool in_interval(unsigned vidx, unsigned offset) const {
        return ge_lower(vidx, offset) && lt_upper(vidx, offset);
    }

    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Macro:
            return false;
        case expr_kind::Var:
            return in_interval(var_idx(e), offset);
        case expr_kind::App:    case expr_kind::Let:
        case expr_kind::Meta:   case expr_kind::Local:
        case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
        case expr_kind::Pair:   case expr_kind::Fst: case expr_kind::Snd:
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
        case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Macro:
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Meta:   case expr_kind::Local:
            result = apply(mlocal_type(e), offset);
        case expr_kind::App:
            result = apply(app_fn(e), offset) || apply(app_arg(e), offset);
            break;
        case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
            result = apply(binder_domain(e), offset) || apply(binder_body(e), offset + 1);
            break;
        case expr_kind::Let:
            result = apply(let_type(e), offset) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
            break;
        case expr_kind::Fst: case expr_kind::Snd:
            result = apply(proj_arg(e), offset);
            break;
        case expr_kind::Pair:
            result = apply(pair_first(e), offset) || apply(pair_second(e), offset) || apply(pair_type(e), offset);
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
    return high > low && !closed(e) && has_free_var_in_range_fn(low, high)(e);
}
bool has_free_var(expr const & e, unsigned i) { return has_free_var(e, i, i+1); }

bool has_free_var_ge(expr const & e, unsigned low) {
    return has_free_var(e, low, std::numeric_limits<unsigned>::max());
}

expr lower_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || closed(e))
        return e;
    lean_assert(s >= d);
    lean_assert(!has_free_var(e, s-d, s));
    return replace(e, [=](expr const & e, unsigned offset) -> expr {
            if (is_var(e) && var_idx(e) >= s + offset) {
                lean_assert(var_idx(e) >= offset + d);
                return mk_var(var_idx(e) - d);
            } else {
                return e;
            }
        });
}
expr lower_free_vars(expr const & e, unsigned d) { return lower_free_vars(e, d, d); }

expr lift_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || closed(e))
        return e;
    return replace(e, [=](expr const & e, unsigned offset) -> expr {
            if (is_var(e) && var_idx(e) >= s + offset) {
                return mk_var(var_idx(e) + d);
            } else {
                return e;
            }
        });
}
expr lift_free_vars(expr const & e, unsigned d) { return lift_free_vars(e, 0, d); }
}
