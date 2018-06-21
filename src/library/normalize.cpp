/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/interrupt.h"
#include "util/fresh_name.h"
#include "kernel/old_type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/replace_visitor.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/attribute_manager.h"

namespace lean {
class normalize_fn {
    abstract_type_context &           m_ctx;
    std::function<bool(expr const &)> m_pred;  // NOLINT
    bool                              m_use_eta;
    bool                              m_eval_nested_prop;

    environment const & env() const { return m_ctx.env(); }

    expr normalize_binding(expr const & e) {
        expr d = normalize(binding_domain(e));
        expr l = m_ctx.push_local(binding_name(e), d, binding_info(e));
        expr b = abstract(normalize(instantiate(binding_body(e), l)), 1, &l);
        m_ctx.pop_local();
        return update_binding(e, d, b);
    }

    optional<expr> is_constructor_like(expr const & e) {
        if (is_constructor_app(env(), e))
            return some_expr(e);
        else
            return none_expr();
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

    bool is_prop(expr const & e) {
        return m_ctx.whnf(m_ctx.infer(e)) == mk_Prop();
    }

    expr normalize_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args) {
            expr new_a = a;
            if (m_eval_nested_prop || !is_prop(m_ctx.infer(a)))
                new_a = normalize(a);
            if (new_a != a)
                modified = true;
            a = new_a;
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
        e = m_ctx.whnf(e);
        switch (e.kind()) {
        case expr_kind::BVar: case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::MVar: case expr_kind::FVar:  case expr_kind::Lit:
            return e;
        case expr_kind::MData:
            lean_unreachable();
        case expr_kind::Proj:
            lean_unreachable();
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

        case expr_kind::Quote:
            return e;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    normalize_fn(abstract_type_context & ctx, bool eta, bool nested_prop = true):
        m_ctx(ctx), m_pred([](expr const &) { return true; }),
        m_use_eta(eta), m_eval_nested_prop(nested_prop) {
    }

    normalize_fn(abstract_type_context & ctx, std::function<bool(expr const &)> const & fn, bool eta, bool nested_prop = true): // NOLINT
        m_ctx(ctx), m_pred(fn), m_use_eta(eta), m_eval_nested_prop(nested_prop) {
    }

    expr operator()(expr const & e) {
        return normalize(e);
    }
};

expr normalize(environment const & env, expr const & e, bool eta) {
    old_type_checker ctx(env);
    return normalize_fn(ctx, eta)(e);
}

expr normalize(abstract_type_context & ctx, expr const & e, bool eta) {
    return normalize_fn(ctx, eta)(e);
}
}
