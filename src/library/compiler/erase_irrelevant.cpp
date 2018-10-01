/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/compiler/util.h"

namespace lean {
static bool is_runtime_atomic_type(name const & n) {
    return
        n == get_uint8_name() ||
        n == get_uint16_name() ||
        n == get_uint32_name() ||
        n == get_uint64_name() ||
        n == get_usize_name() ||
        n == get_bool_name() ||
        n == get_unit_name() ||
        n == get_string_name();
}

class erase_irrelevant_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;

    environment & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr mk_runtime_type(expr e, bool atomic_only = false) {
        type_checker tc(m_st, m_lctx);
        e = tc.whnf(e);
        if (is_constant(e)) {
            name const & c = const_name(e);
            if (is_runtime_atomic_type(c))
                return e;
            else if (c == get_char_name())
                return mk_constant(get_uint32_name());
            else
                return mk_enf_object_type();
        } else if (!atomic_only && is_app_of(e, get_array_name(), 1)) {
            expr t = mk_runtime_type(app_arg(e), true);
            return mk_app(app_fn(e), t);
        } else if (is_sort(e)) {
            return is_zero(sort_level(e)) ? mk_Prop() : mk_Type();
        } else if (tc.is_prop(e)) {
            return mk_true();
        } else {
            return mk_enf_object_type();
        }
    }

    expr visit_constant(expr const & e) {
        lean_assert(!is_enf_neutral(e));
        type_checker tc(m_st, m_lctx);
        expr e_type = tc.whnf(tc.infer(e));
        if (tc.is_prop(e_type) || is_sort(e_type))
            return mk_enf_neutral();
        else
            return mk_constant(const_name(e));
    }

    bool is_atom(expr const & e) {
        switch (e.kind()) {
        case expr_kind::FVar:   return true;
        case expr_kind::Lit:    return true;
        case expr_kind::Const:  return true;
        default: return false;
        }
    }

    expr visit_cases_on(expr const & c, buffer<expr> & args) {
        unsigned minors_begin; unsigned minors_end;
        std::tie(minors_begin, minors_end) = get_cases_on_minors_range(env(), const_name(c));
        for (unsigned i = 0; i < minors_begin - 1; i++)
            args[i] = mk_enf_neutral();
        for (unsigned i = minors_begin - 1; i < minors_end; i++) {
            args[i] = visit(args[i]);
        }
        return mk_app(c, args);
    }

    expr visit_app_default(expr const & fn, buffer<expr> & args) {
        for (expr & arg : args) {
            if (!is_atom(arg)) {
                // In LCNF, relevant arguments are atomic
                arg = mk_enf_neutral();
            } else if (is_constant(arg)) {
                arg = visit_constant(arg);
            }
        }
        return mk_app(fn, args);
    }

    expr visit_quot_lift(buffer<expr> & args) {
        lean_assert(args.size() >= 6);
        expr f = visit(args[3]);
        buffer<expr> new_args;
        for (unsigned i = 5; i < args.size(); i++)
            new_args.push_back(args[i]);
        return visit_app_default(f, new_args);
    }

    expr visit_quot_mk(buffer<expr> const & args) {
        lean_assert(args.size() == 3);
        return visit(args[2]);
    }

    expr visit_app(expr const & e) {
        buffer<expr> args;
        expr f = visit(get_app_args(e, args));
        if (is_constant(f)) {
            name const & fn = const_name(f);
            if (fn == get_lc_proof_name()) {
                return mk_enf_neutral();
            } else if (is_cases_on_recursor(env(), fn)) {
                return visit_cases_on(f, args);
            } else if (fn == get_quot_mk_name()) {
                return visit_quot_mk(args);
            } else if (fn == get_quot_lift_name()) {
                return visit_quot_lift(args);
            }
        }
        return visit_app_default(f, args);
    }

    expr visit_lambda(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        buffer<pair<name, expr>> entries;
        while (is_lambda(e)) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            expr d    = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), d, binding_info(e));
            fvars.push_back(fvar);
            entries.emplace_back(binding_name(e), mk_runtime_type(d));
            e = binding_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        r      = abstract(r, fvars.size(), fvars.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            r = mk_lambda(entries[i].first, entries[i].second, r);
        }
        return r;
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        buffer<std::tuple<name, expr, expr>> entries;
        while (is_let(e)) {
            expr t    = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            expr v    = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            expr fvar = m_lctx.mk_local_decl(ngen(), let_name(e), t, v);
            fvars.push_back(fvar);
            entries.emplace_back(let_name(e), mk_runtime_type(t), visit(v));
            e = let_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        r      = abstract(r, fvars.size(), fvars.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr v = abstract(std::get<2>(entries[i]), i, fvars.data());
            r      = mk_let(std::get<0>(entries[i]), std::get<1>(entries[i]), v, r);
        }
        return r;
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::BVar:  case expr_kind::MVar:
            lean_unreachable();
        case expr_kind::FVar:   return e;
        case expr_kind::Sort:   return mk_enf_neutral();
        case expr_kind::Lit:    return e;
        case expr_kind::Pi:     return mk_enf_neutral();
        case expr_kind::Const:  return visit_constant(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Proj:   return e;
        case expr_kind::MData:  return e;
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        }
        lean_unreachable();
    }
public:
    erase_irrelevant_fn(environment const & env, local_ctx const & lctx):
        m_st(env), m_lctx(lctx) {}
    expr operator()(expr const & e) { return visit(e); }
};

expr erase_irrelevant(environment const & env, local_ctx const & lctx, expr const & e) {
    return erase_irrelevant_fn(env, lctx)(e);
}
}
