/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/fresh_name.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/inductive/inductive.h"
#include "library/replace_visitor.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/attribute_manager.h"
#include "library/old_type_checker.h"

namespace lean {
/**
   \brief unfold hints instruct the normalizer (and simplifier) that
   a function application. We have two kinds of hints:
   - [unfold] (f a_1 ... a_i ... a_n) should be unfolded
     when argument a_i is a constructor.
   - [unfold-full] (f a_1 ... a_i ... a_n) should be unfolded when it is fully applied.
   - constructor (f ...) should be unfolded when it is the major premise of a recursor-like operator
*/

environment add_unfold_hint(environment const & env, name const & n, list<unsigned> const & idxs, bool persistent) {
    return set_attribute(env, get_dummy_ios(), "unfold", n, LEAN_DEFAULT_PRIORITY, idxs, persistent);
}
list<unsigned> has_unfold_hint(environment const & env, name const & d) {
    if (has_attribute(env, "unfold", d))
        return get_attribute_params(env, "unfold", d);
    else
        return list<unsigned>();
}

bool has_unfold_full_hint(environment const & env, name const & d) {
    return has_attribute(env, "unfold_full", d);
}

bool has_constructor_hint(environment const & env, name const & d) {
    return has_attribute(env, "constructor", d);
}

void initialize_normalize() {
    register_attribute(unsigned_params_attribute("unfold", "unfold definition when the given positions are constructors"));
    register_attribute(basic_attribute("unfold_full", "instructs normalizer (and simplifier) that function application (f a_1 ... a_n) should be unfolded when it is fully applied"));
    register_attribute(basic_attribute("constructor", "instructs normalizer (and simplifier) that function application (f ...) should be unfolded when it is the major premise of a constructor like operator"));
}

void finalize_normalize() {
}

class normalize_fn {
    old_type_checker   &                  m_tc;
    // Remark: the normalizer/type-checker m_tc has been provided by the "user".
    // It may be a constrained one (e.g., it may only unfold definitions marked as [reducible].
    // So, we should not use it for inferring types and/or checking whether an expression is
    // a proposition or not. Such checks may fail because of the restrictions on m_tc.
    // So, we use m_full_tc for this kind of operation. It is an unconstrained type checker.
    // See issue #801
    old_type_checker                      m_full_tc;
    std::function<bool(expr const &)> m_pred;  // NOLINT
    bool                              m_save_cnstrs;
    constraint_seq                    m_cnstrs;
    bool                              m_use_eta;
    bool                              m_eval_nested_prop;

    environment const & env() const { return m_tc.env(); }

    expr normalize_binding(expr const & e) {
        expr d = normalize(binding_domain(e));
        expr l = mk_local(mk_fresh_name(), binding_name(e), d, binding_info(e));
        expr b = abstract(normalize(instantiate(binding_body(e), l)), l);
        return update_binding(e, d, b);
    }

    list<unsigned> has_unfold_hint(expr const & f) {
        if (!is_constant(f))
            return list<unsigned>();
        return ::lean::has_unfold_hint(env(), const_name(f));
    }

    bool has_unfold_full_hint(expr const & f) {
        return is_constant(f) &&  ::lean::has_unfold_full_hint(env(), const_name(f));
    }

    optional<expr> is_constructor_like(expr const & e) {
        if (is_constructor_app(env(), e))
            return some_expr(e);
        expr const & f = get_app_fn(e);
        if (is_constant(f) && has_constructor_hint(env(), const_name(f))) {
            if (auto r = unfold_term(env(), e))
                return r;
            else
                return some_expr(e);
        } else {
            return none_expr();
        }
    }

    optional<expr> unfold_recursor_core(expr const & f, unsigned i,
                                        buffer<unsigned> const & idxs, buffer<expr> & args, bool is_rec) {
        if (i == idxs.size()) {
            expr new_app = mk_rev_app(f, args);
            if (is_rec)
                return some_expr(normalize(new_app));
            else if (optional<expr> r = unfold_app(env(), new_app))
                return some_expr(normalize(*r));
            else
                return none_expr();
        } else {
            unsigned idx = idxs[i];
            if (idx >= args.size())
                return none_expr();
            expr & arg = args[args.size() - idx - 1];
            optional<expr> new_arg = is_constructor_like(arg);
            if (!new_arg)
                return none_expr();
            flet<expr> set_arg(arg, *new_arg);
            return unfold_recursor_core(f, i+1, idxs, args, is_rec);
        }
    }

    optional<expr> unfold_recursor_like(expr const & f, list<unsigned> const & idx_lst, buffer<expr> & args) {
        buffer<unsigned> idxs;
        to_buffer(idx_lst, idxs);
        return unfold_recursor_core(f, 0, idxs, args, false);
    }

    optional<expr> unfold_recursor_major(expr const & f, unsigned idx, buffer<expr> & args) {
        buffer<unsigned> idxs;
        idxs.push_back(idx);
        return unfold_recursor_core(f, 0, idxs, args, true);
    }

    expr normalize_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args) {
            expr new_a = a;
            if (m_eval_nested_prop || !m_full_tc.is_prop(m_full_tc.infer(a).first).first)
                 new_a = normalize(a);
            if (new_a != a)
                modified = true;
            a = new_a;
        }
        if (has_unfold_full_hint(f)) {
            if (!is_pi(m_full_tc.whnf(m_full_tc.infer(e).first).first)) {
                if (optional<expr> r = unfold_app(env(), mk_rev_app(f, args))) {
                    return normalize(*r);
                }
            }
        }
        if (auto idxs = has_unfold_hint(f)) {
            if (auto r = unfold_recursor_like(f, idxs, args))
                return *r;
        }
        if (is_constant(f)) {
            if (auto idx = inductive::get_elim_major_idx(env(), const_name(f))) {
                if (auto r = unfold_recursor_major(f, *idx, args))
                    return *r;
            }
        }
        if (!modified)
            return e;
        expr r = mk_rev_app(f, args);
        if (is_constant(f) && env().is_recursor(const_name(f))) {
            return normalize(r);
        } else {
            return r;
        }
    }

    expr normalize(expr e) {
        check_system("normalize");
        if (!m_pred(e))
            return e;
        auto w = m_tc.whnf(e);
        e = w.first;
        if (m_save_cnstrs)
            m_cnstrs += w.second;
        switch (e.kind()) {
        case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
        case expr_kind::Meta: case expr_kind::Local: case expr_kind::Macro:
            return e;
        case expr_kind::Lambda: {
            e = normalize_binding(e);
            if (m_use_eta)
                return try_eta(e);
            else
                return e;
        }
        case expr_kind::Pi:
            return normalize_binding(e);
        case expr_kind::App:
            return normalize_app(e);
        case expr_kind::Let:
            // whnf unfolds let-exprs
            lean_unreachable();
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    normalize_fn(old_type_checker & tc, bool save, bool eta, bool nested_prop = true):
        m_tc(tc), m_full_tc(tc.env()),
        m_pred([](expr const &) { return true; }),
        m_save_cnstrs(save), m_use_eta(eta), m_eval_nested_prop(nested_prop) {
        if (!is_standard(env()))
            m_eval_nested_prop = true;
    }

    normalize_fn(old_type_checker & tc, std::function<bool(expr const &)> const & fn, bool eta, bool nested_prop = true): // NOLINT
        m_tc(tc), m_full_tc(tc.env()),
        m_pred(fn), m_save_cnstrs(true), m_use_eta(eta), m_eval_nested_prop(nested_prop) {
        if (!is_standard(env()))
            m_eval_nested_prop = true;
    }

    expr operator()(expr const & e) {
        m_cnstrs = constraint_seq();
        return normalize(e);
    }

    expr operator()(level_param_names const & ls, expr const & e) {
        m_cnstrs = constraint_seq();
        return m_tc.with_params(ls, [&]() {
                return normalize(e);
            });
    }

    constraint_seq get_cnstrs() const { return m_cnstrs; }
};

expr normalize(environment const & env, expr const & e, bool eta) {
    auto tc          = mk_type_checker(env);
    bool save_cnstrs = false;
    return normalize_fn(*tc, save_cnstrs, eta)(e);
}

expr normalize(environment const & env, level_param_names const & ls, expr const & e, bool eta) {
    auto tc          = mk_type_checker(env);
    bool save_cnstrs = false;
    return normalize_fn(*tc, save_cnstrs, eta)(ls, e);
}

expr normalize(old_type_checker & tc, expr const & e, bool eta) {
    bool save_cnstrs = false;
    return normalize_fn(tc, save_cnstrs, eta)(e);
}

expr normalize(old_type_checker & tc, level_param_names const & ls, expr const & e, bool eta, bool eval_nested_prop) {
    bool save_cnstrs = false;
    return normalize_fn(tc, save_cnstrs, eta, eval_nested_prop)(ls, e);
}

expr normalize(old_type_checker & tc, expr const & e, constraint_seq & cs, bool eta) {
    bool save_cnstrs = false;
    normalize_fn fn(tc, save_cnstrs, eta);
    expr r = fn(e);
    cs += fn.get_cnstrs();
    return r;
}

expr normalize(old_type_checker & tc, expr const & e, std::function<bool(expr const &)> const & pred, // NOLINT
               constraint_seq & cs, bool eta) {
    normalize_fn fn(tc, pred, eta);
    expr r = fn(e);
    cs += fn.get_cnstrs();
    return r;
}
}
