/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/type_context.h"
#include "library/locals.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

namespace lean {
[[ noreturn ]] static void throw_ill_formed_eqns() {
    throw exception("ill-formed match/equations expression");
}

static optional<pair<expr, unsigned>> get_eqn_fn_and_arity(expr e) {
    while (is_lambda(e))
        e = binding_body(e);
    if (!is_equation(e) && !is_no_equation(e)) throw_ill_formed_eqns();
    if (is_no_equation(e)) {
        return optional<pair<expr, unsigned>>();
    } else {
        expr const & lhs = equation_lhs(e);
        expr const & fn  = get_app_fn(lhs);
        lean_assert(is_local(fn));
        return optional<pair<expr, unsigned>>(fn, get_app_num_args(lhs));
    }
}

static expr consume_fn_prefix(expr eq, buffer<expr> const & fns) {
    for (unsigned i = 0; i < fns.size(); i++) {
        if (!is_lambda(eq)) throw_ill_formed_eqns();
        eq = binding_body(eq);
    }
    return instantiate_rev(eq, fns);
}

void equations_editor::unpack(expr const & e) {
    m_fns.clear();
    m_arity.clear();
    m_eqs.clear();
    lean_assert(is_equations(e));
    m_src = e;
    buffer<expr> eqs;
    unsigned num_fns = equations_num_fns(e);
    to_equations(e, eqs);
    /* Extract functions. */
    lean_assert(eqs.size() > 0);
    expr eq = eqs[0];
    for (unsigned i = 0; i < num_fns; i++) {
        lean_assert(is_lambda(eq));
        m_fns.push_back(mk_local(binding_name(eq), binding_domain(eq)));
        eq = binding_body(eq);
    }
    /* Extract equations */
    unsigned eqidx = 0;
    for (unsigned fidx = 0; fidx < num_fns; fidx++) {
        m_eqs.push_back(buffer<expr>());
        buffer<expr> & fn_eqs = m_eqs.back();
        if (eqidx >= eqs.size()) throw_ill_formed_eqns();
        expr eq = consume_fn_prefix(eqs[eqidx], m_fns);
        fn_eqs.push_back(eq);
        eqidx++;
        if (auto p = get_eqn_fn_and_arity(eq)) {
            if (p->first != m_fns[fidx]) throw_ill_formed_eqns();
            unsigned arity = p->second;
            m_arity.push_back(arity);
            while (eqidx < eqs.size()) {
                expr eq = consume_fn_prefix(eqs[eqidx], m_fns);
                if (auto p = get_eqn_fn_and_arity(eq)) {
                    if (p->first == m_fns[fidx]) {
                        if (p->second != arity) throw_ill_formed_eqns();
                        fn_eqs.push_back(eq);
                        eqidx++;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        } else {
            /* noequation, guess arity using type of function */
            expr type = mlocal_type(m_fns[fidx]);
            unsigned arity = 0;
            while (is_pi(type))
                type = binding_body(type);
            if (arity == 0) throw_ill_formed_eqns();
            m_arity.push_back(arity);
        }
    }
    if (eqs.size() != eqidx) throw_ill_formed_eqns();
    lean_assert(m_arity.size() == m_fns.size());
    lean_assert(m_eqs.size() == m_fns.size());
}

expr equations_editor::repack() {
    buffer<expr> new_eqs;
    for (buffer<expr> const & fn_eqs : m_eqs) {
        for (expr const & eq : fn_eqs) {
            new_eqs.push_back(Fun(m_fns, eq));
        }
    }
    return update_equations(m_src, new_eqs);
}

struct sigma_packer_fn {
    type_context & m_ctx;
    sigma_packer_fn(type_context & ctx):m_ctx(ctx) {}

    expr_pair mk_sigma_domain(expr const & pi_type, buffer<expr> & out_locals, unsigned n) {
        if (n == 0) return mk_pair(mk_constant(get_unit_name()), pi_type);
        expr type = pi_type;
        if (!is_pi(type)) type = m_ctx.relaxed_whnf(type);
        if (!is_pi(type)) throw_ill_formed_eqns();
        expr const & A = binding_domain(type);
        type_context::tmp_locals locals(m_ctx);
        expr a = locals.push_local_from_binding(type);
        out_locals.push_back(a);
        expr B, codomain;
        std::tie(B, codomain) = mk_sigma_domain(instantiate(binding_body(type), a), out_locals, n-1);
        B = locals.mk_lambda(B);
        return mk_pair(mk_app(m_ctx, get_sigma_name(), A, B), codomain);
    }

    expr mk_codomain(expr const & codomain, expr p, buffer<expr> const & locals, unsigned n) {
        buffer<expr> terms;
        for (unsigned i = 0; i < n; i++) {
            terms.push_back(mk_app(m_ctx, get_sigma_pr1_name(), p));
            p = mk_app(m_ctx, get_sigma_pr2_name(), p);
        }
        return replace_locals(codomain, locals, terms);
    }

    expr pack_as_unary(expr const & pi_type, unsigned n) {
        buffer<expr> locals;
        expr domain, pre_codomain;
        std::tie(domain, pre_codomain) = mk_sigma_domain(pi_type, locals, n);
        type_context::tmp_locals plocal(m_ctx);
        expr p = plocal.push_local("_p", domain);
        expr codomain = mk_codomain(pre_codomain, p, locals, n);
        return plocal.mk_pi(codomain);
    }

    class update_apps_fn : public replace_visitor_with_tc {
        buffer<expr> const &     m_old_fns;
        equations_editor const & m_editor;

        optional<unsigned> get_fn_idx(expr const & fn) {
            if (!is_local(fn)) return optional<unsigned>();
            for (unsigned fnidx = 0; fnidx < m_old_fns.size(); fnidx++) {
                if (mlocal_name(fn) == mlocal_name(m_old_fns[fnidx]))
                    return optional<unsigned>(fnidx);
            }
            return optional<unsigned>();
        }

        expr pack(unsigned i, unsigned arity, buffer<expr> const & args, expr const & type) {
            if (i == arity) {
                lean_assert(is_constant(type, get_unit_name()));
                return mk_constant(get_unit_star_name());
            } else {
                lean_assert(is_constant(get_app_fn(type), get_sigma_name()));
                expr a        = args[i];
                expr A        = app_arg(app_fn(type));
                expr B        = app_arg(type);
                lean_assert(is_lambda(B));
                expr new_type = instantiate(binding_body(B), a);
                expr b        = pack(i+1, arity, args, new_type);
                bool mask[2]  = {true, true};
                expr AB[2]    = {A, B};
                return mk_app(mk_app(m_ctx, get_sigma_mk_name(), 2, mask, AB), a, b);
            }
        }

        virtual expr visit_app(expr const & e) override {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            auto fnidx = get_fn_idx(fn);
            if (!fnidx) return replace_visitor_with_tc::visit_app(e);
            expr new_fn = m_editor.get_fn(*fnidx);
            if (fn == new_fn) return replace_visitor_with_tc::visit_app(e);
            unsigned arity = m_editor.get_arity(*fnidx);
            if (args.size() < arity) {
                expr new_e = m_ctx.eta_expand(e);
                if (!is_lambda(new_e)) throw_ill_formed_eqns();
                return visit(new_e);
            }
            expr new_fn_type = m_ctx.infer(new_fn);
            expr sigma_type  = binding_domain(new_fn_type);
            expr arg         = pack(0, arity, args, sigma_type);
            expr r           = mk_app(new_fn, arg);
            return mk_app(r, args.size() - arity, args.data() + arity);
        }

    public:
        update_apps_fn(type_context & ctx, buffer<expr> const & old_fns, equations_editor const & editor):
            replace_visitor_with_tc(ctx), m_old_fns(old_fns), m_editor(editor) {}
    };

    expr operator()(expr const & e) {
        equations_editor editor;
        editor.unpack(e);
        buffer<expr> old_fns;
        bool modified = false;
        for (unsigned fidx = 0; fidx < editor.get_num_fns(); fidx++) {
            expr & fn = editor.get_fn(fidx);
            old_fns.push_back(fn);
            unsigned arity = editor.get_arity(fidx);
            if (arity > 1) {
                expr new_type = pack_as_unary(mlocal_type(fn), arity);
                fn = update_mlocal(fn, new_type);
                modified = true;
            }
        }
        if (!modified) return e;
        update_apps_fn updt(m_ctx, old_fns, editor);
        for (unsigned fidx = 0; fidx < editor.get_num_fns(); fidx++) {
            buffer<expr> & eqs = editor.get_eqs_of(fidx);
            for (expr & eq : eqs)
                eq = updt(eq);
        }
        return editor.repack();
    }
};

expr pack_equations_domain(type_context & ctx, expr const & e) {
    return sigma_packer_fn(ctx)(e);
}
}
