/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/free_vars.h"
#include "kernel/expr_sets.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
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

    bool apply(optional<expr> const & e, unsigned offset) {
        return e && apply(*e, offset);
    }

    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant:
            if (!const_type(e))
                return false;
            break;
        case expr_kind::Type: case expr_kind::Value:
            return false;
        case expr_kind::MetaVar:
            return true;
        case expr_kind::Var:
            return var_idx(e) >= offset;
        case expr_kind::App: case expr_kind::HEq: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Let:
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
        case expr_kind::Constant:
            lean_assert(const_type(e));
            result = apply(const_type(e), offset);
            break;
        case expr_kind::Type: case expr_kind::Value: case expr_kind::Var: case expr_kind::MetaVar:
            // easy cases were already handled
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::App:
            result = std::any_of(begin_args(e), end_args(e), [=](expr const & arg){ return apply(arg, offset); });
            break;
        case expr_kind::HEq:
            result = apply(heq_lhs(e), offset) || apply(heq_rhs(e), offset);
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            result = apply(abst_domain(e), offset) || apply(abst_body(e), offset + 1);
            break;
        case expr_kind::Let:
            result = apply(let_type(e), offset) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
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
    metavar_env const & m_menv;

    static unsigned dec(unsigned s) { return (s == 0) ? 0 : s - 1; }

    /*
      \brief If a metavariable \c m was defined in a context \c ctx and <tt>ctx.size() == R</tt>,
      then \c m can only contain free variables in the range <tt>[0, R)</tt>

      So, if \c m does not have an associated local context, the answer is just \c R.
      If \c m has an associated local context, we process it using the following rules

           [inst:s v] R  ===>  if s >= R then R else max(R-1, range_of(v))
           [lift:s:n] R  ===>  if s >= R then R else R + n
    */
    unsigned process_metavar(expr const & m) {
        lean_assert(is_metavar(m));
        context ctx = m_menv->get_context(metavar_name(m));
        unsigned R  = ctx.size();
        if (has_local_context(m)) {
            local_context lctx = metavar_lctx(m);
            buffer<local_entry> lentries;
            to_buffer(lctx, lentries);
            unsigned i = lentries.size();
            while (i > 0) {
                --i;
                local_entry const & entry = lentries[i];
                if (entry.is_inst()) {
                    if (entry.s() < R) {
                        R = std::max(dec(R), apply(entry.v()));
                    }
                } else {
                    if (entry.s() < R)
                        R += entry.n();
                }
            }
        }
        return R;
    }

    unsigned apply(optional<expr> const & e) {
        return e ? apply(*e) : 0;
    }

    unsigned apply(expr const & e) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant:
            if (!const_type(e))
                return 0;
            break;
        case expr_kind::Type: case expr_kind::Value:
            return 0;
        case expr_kind::Var:
            return var_idx(e) + 1;
        case expr_kind::MetaVar: case expr_kind::App: case expr_kind::HEq:
        case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Let:
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
        case expr_kind::Constant:
            lean_assert(const_type(e));
            result = apply(const_type(e));
            break;
        case expr_kind::Type: case expr_kind::Value: case expr_kind::Var:
            // easy cases were already handled
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MetaVar:
            result = process_metavar(e);
            break;
        case expr_kind::App:
            for (auto const & c : args(e))
                result = std::max(result, apply(c));
            break;
        case expr_kind::HEq:
            result = std::max(apply(heq_lhs(e)), apply(heq_rhs(e)));
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            result = std::max(apply(abst_domain(e)), dec(apply(abst_body(e))));
            break;
        case expr_kind::Let:
            result = std::max({apply(let_type(e)), apply(let_value(e)), dec(apply(let_body(e)))});
            break;
        }

        if (shared)
            m_cached.insert(mk_pair(e, result));

        return result;
    }
public:
    free_var_range_fn(metavar_env const & menv):m_menv(menv) {}
    unsigned operator()(expr const & e) { return apply(e); }
};

unsigned free_var_range(expr const & e, metavar_env const & menv) {
    return free_var_range_fn(menv)(e);
}

/**
    \brief Functional object for checking whether a kernel expression has a free variable in the range <tt>[low, high)</tt> or not.

    \remark We assume that a metavariable contains free variables.
    This is an approximation, since we don't know how the metavariable will be instantiated.
*/
class has_free_var_in_range_fn {
protected:
    unsigned                           m_low;
    unsigned                           m_high;
    expr_cell_offset_set               m_cached;
    std::unique_ptr<free_var_range_fn> m_range_fn;

    bool apply(optional<expr> const & e, unsigned offset) {
        return e && apply(*e, offset);
    }

    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant:
            if (!const_type(e))
                return false;
            break;
        case expr_kind::Type: case expr_kind::Value:
            return false;
        case expr_kind::MetaVar:
            if (m_range_fn)
                break; // it is not cheap
            else
                return true; // assume that any free variable can occur in the metavariable
        case expr_kind::Var:
            return var_idx(e) >= offset + m_low && var_idx(e) < offset + m_high;
        case expr_kind::App: case expr_kind::HEq: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Let:
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
        case expr_kind::Constant:
            lean_assert(const_type(e));
            result = apply(const_type(e), offset);
            break;
        case expr_kind::Type: case expr_kind::Value: case expr_kind::Var:
            // easy cases were already handled
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MetaVar: {
            lean_assert(m_range_fn);
            unsigned R = (*m_range_fn)(e);
            if (R > 0) {
                unsigned max_fvar_idx = R - 1;
                result = max_fvar_idx >= offset + m_low;
                // Remark: Variable #0 may occur in \c e.
                // So, we don't have to check the upper bound offset + m_high;
            }
            break;
        }
        case expr_kind::App:
            result = std::any_of(begin_args(e), end_args(e), [=](expr const & arg){ return apply(arg, offset); });
            break;
        case expr_kind::HEq:
            result = apply(heq_lhs(e), offset) || apply(heq_rhs(e), offset);
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            result = apply(abst_domain(e), offset) || apply(abst_body(e), offset + 1);
            break;
        case expr_kind::Let:
            result = apply(let_type(e), offset) || apply(let_value(e), offset) || apply(let_body(e), offset + 1);
            break;
        }

        if (!result && shared) {
            m_cached.insert(expr_cell_offset(e.raw(), offset));
        }

        return result;
    }
public:
    has_free_var_in_range_fn(unsigned low, unsigned high, optional<metavar_env> const & menv):
        m_low(low),
        m_high(high) {
        lean_assert(low < high);
        if (menv)
            m_range_fn.reset(new free_var_range_fn(*menv));
    }
    bool operator()(expr const & e) { return apply(e, 0); }
};

bool has_free_var(expr const & e, unsigned low, unsigned high, optional<metavar_env> const & menv) { return has_free_var_in_range_fn(low, high, menv)(e); }
bool has_free_var(expr const & e, unsigned low, unsigned high, metavar_env const & menv) { return has_free_var(e, low, high, some_menv(menv)); }
bool has_free_var(expr const & e, unsigned low, unsigned high) { return has_free_var(e, low, high, none_menv()); }
bool has_free_var(expr const & e, unsigned i, optional<metavar_env> const & menv) { return has_free_var(e, i, i+1, menv); }
bool has_free_var(expr const & e, unsigned i, metavar_env const & menv) { return has_free_var(e, i, i+1, menv); }
bool has_free_var(expr const & e, unsigned i) { return has_free_var(e, i, i+1); }

bool has_free_var(context_entry const & e, unsigned low, unsigned high, metavar_env const & menv) {
    auto d = e.get_domain();
    auto b = e.get_body();
    return (d && has_free_var(*d, low, high, menv)) || (b && has_free_var(*b, low, high, menv));
}

expr lower_free_vars(expr const & e, unsigned s, unsigned d, optional<metavar_env> const & DEBUG_CODE(menv)) {
    lean_assert(s >= d);
    lean_assert(!has_free_var(e, s-d, s, menv));
    return replace(e, [=](expr const & e, unsigned offset) -> expr {
            if (is_var(e) && var_idx(e) >= s + offset) {
                lean_assert(var_idx(e) >= offset + d);
                return mk_var(var_idx(e) - d);
            } else {
                return e;
            }
        });
}
expr lower_free_vars(expr const & e, unsigned s, unsigned d, metavar_env const & menv) { return lower_free_vars(e, s, d, some_menv(menv)); }
expr lower_free_vars(expr const & e, unsigned s, unsigned d) { return lower_free_vars(e, s, d, none_menv()); }
expr lower_free_vars(expr const & e, unsigned d, optional<metavar_env> const & menv) { return lower_free_vars(e, d, d, menv); }
expr lower_free_vars(expr const & e, unsigned d, metavar_env const & menv) { return lower_free_vars(e, d, d, menv); }
expr lower_free_vars(expr const & e, unsigned d) { return lower_free_vars(e, d, d); }

context_entry lower_free_vars(context_entry const & e, unsigned s, unsigned d, metavar_env const & menv) {
    auto domain = e.get_domain();
    auto body   = e.get_body();
    if (domain && body)
        return context_entry(e.get_name(), lower_free_vars(*domain, s, d, menv), lower_free_vars(*body, s, d, menv));
    else if (domain)
        return context_entry(e.get_name(), lower_free_vars(*domain, s, d, menv));
    else
        return context_entry(e.get_name(), none_expr(), lower_free_vars(*body, s, d, menv));
}

expr lift_free_vars(expr const & e, unsigned s, unsigned d, optional<metavar_env> const & menv) {
    if (d == 0)
        return e;
    return replace(e, [=](expr const & e, unsigned offset) -> expr {
            if (is_var(e) && var_idx(e) >= s + offset) {
                return mk_var(var_idx(e) + d);
            } else if (is_metavar(e)) {
                return add_lift(e, s + offset, d, menv);
            } else {
                return e;
            }
        });
}
expr lift_free_vars(expr const & e, unsigned s, unsigned d, metavar_env const & menv) { return lift_free_vars(e, s, d, some_menv(menv)); }
expr lift_free_vars(expr const & e, unsigned s, unsigned d) { return lift_free_vars(e, s, d, none_menv()); }
expr lift_free_vars(expr const & e, unsigned d, optional<metavar_env> const & menv) { return lift_free_vars(e, 0, d, menv); }
expr lift_free_vars(expr const & e, unsigned d) { return lift_free_vars(e, 0, d); }
expr lift_free_vars(expr const & e, unsigned d, metavar_env const & menv) { return lift_free_vars(e, 0, d, menv); }

context_entry lift_free_vars(context_entry const & e, unsigned s, unsigned d, metavar_env const & menv) {
    auto domain = e.get_domain();
    auto body   = e.get_body();
    if (domain && body)
        return context_entry(e.get_name(), lift_free_vars(*domain, s, d, menv), lift_free_vars(*body, s, d, menv));
    else if (domain)
        return context_entry(e.get_name(), lift_free_vars(*domain, s, d, menv));
    else
        return context_entry(e.get_name(), none_expr(), lift_free_vars(*body, s, d, menv));
}

optional<unsigned> max_free_var(expr const & e) {
    optional<unsigned> r;
    for_each(e, [&](expr const & v, unsigned offset) {
            if (is_var(v)) {
                unsigned vidx = var_idx(v);
                if (vidx >= offset) {
                    vidx -= offset;
                    if (!r || vidx > *r)
                        r = vidx;
                }
            }
            return true;
        });
    return r;
}
}
