/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/type_context.h"
#include "library/locals.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

namespace lean {
struct sigma_packer_fn {
    type_context_old & m_ctx;
    sigma_packer_fn(type_context_old & ctx):m_ctx(ctx) {}

    expr_pair mk_sigma_domain(expr const & pi_type, buffer<expr> & out_locals, unsigned n) {
        expr type = pi_type;
        if (!is_pi(type)) type = m_ctx.relaxed_whnf(type);
        if (!is_pi(type)) throw_ill_formed_eqns();
        expr const & A = binding_domain(type);
        type_context_old::tmp_locals locals(m_ctx);
        expr a = locals.push_local_from_binding(type);
        out_locals.push_back(a);
        expr next_pi_type = instantiate(binding_body(type), a);
        if (n == 1) return mk_pair(A, next_pi_type);
        expr B, codomain;
        std::tie(B, codomain) = mk_sigma_domain(next_pi_type, out_locals, n-1);
        B = locals.mk_lambda(B);
        return mk_pair(mk_app(m_ctx, get_psigma_name(), A, B), codomain);
    }

    expr mk_codomain(expr const & codomain, expr p, buffer<expr> const & locals, unsigned n) {
        buffer<expr> terms;
        for (unsigned i = 0; i < n - 1; i++) {
            terms.push_back(mk_app(m_ctx, get_psigma_fst_name(), p));
            p = mk_app(m_ctx, get_psigma_snd_name(), p);
        }
        terms.push_back(p);
        return replace_locals(codomain, locals, terms);
    }

    expr pack_as_unary(expr const & pi_type, unsigned n) {
        buffer<expr> locals;
        expr domain, pre_codomain;
        std::tie(domain, pre_codomain) = mk_sigma_domain(pi_type, locals, n);
        type_context_old::tmp_locals plocal(m_ctx);
        expr p = plocal.push_local("_p", domain);
        expr codomain = mk_codomain(pre_codomain, p, locals, n);
        return plocal.mk_pi(codomain);
    }

    class update_apps_fn : public replace_visitor_with_tc {
        buffer<expr> const & m_old_fns;
        unpack_eqns const &  m_ues;

        optional<unsigned> get_fn_idx(expr const & fn) {
            if (!is_local(fn)) return optional<unsigned>();
            for (unsigned fnidx = 0; fnidx < m_old_fns.size(); fnidx++) {
                if (mlocal_name(fn) == mlocal_name(m_old_fns[fnidx]))
                    return optional<unsigned>(fnidx);
            }
            return optional<unsigned>();
        }

        expr pack(unsigned i, unsigned arity, buffer<expr> const & args, expr const & type) {
            lean_assert(arity > 0);
            if (i == arity - 1) {
                return args[i];
            } else {
                lean_assert(is_constant(get_app_fn(type), get_psigma_name()));
                expr a        = args[i];
                expr A        = app_arg(app_fn(type));
                expr B        = app_arg(type);
                lean_assert(is_lambda(B));
                expr new_type = instantiate(binding_body(B), a);
                expr b        = pack(i+1, arity, args, new_type);
                bool mask[2]  = {true, true};
                expr AB[2]    = {A, B};
                return mk_app(mk_app(m_ctx, get_psigma_mk_name(), 2, mask, AB), a, b);
            }
        }

        virtual expr visit_app(expr const & e) override {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            for (expr & arg : args)
                arg = visit(arg);
            auto fnidx = get_fn_idx(fn);
            if (!fnidx) return replace_visitor_with_tc::visit_app(e);
            expr new_fn = m_ues.get_fn(*fnidx);
            if (fn == new_fn) return replace_visitor_with_tc::visit_app(e);
            unsigned arity = m_ues.get_arity_of(*fnidx);
            if (args.size() < arity) {
                expr new_e = m_ctx.eta_expand(e);
                if (!is_lambda(new_e)) throw_ill_formed_eqns();
                return visit(new_e);
            }
            expr new_fn_type = m_ctx.infer(new_fn);
            expr sigma_type  = binding_domain(new_fn_type);
            expr arg         = pack(0, arity, args, sigma_type);
            expr r           = mk_app(new_fn, arg);
            return copy_tag(e, mk_app(r, args.size() - arity, args.data() + arity));
        }

        virtual expr visit_local(expr const & e) override {
            auto fnidx = get_fn_idx(e);
            if (!fnidx) return replace_visitor_with_tc::visit_local(e);
            expr new_fn = m_ues.get_fn(*fnidx);
            if (e == new_fn) return replace_visitor_with_tc::visit_local(e);
            unsigned arity = m_ues.get_arity_of(*fnidx);
            if (0 < arity) {
                expr new_e = m_ctx.eta_expand(e);
                if (!is_lambda(new_e)) throw_ill_formed_eqns();
                return visit(new_e);
            }
            return new_fn;
        }

    public:
        update_apps_fn(type_context_old & ctx, buffer<expr> const & old_fns, unpack_eqns const & ues):
            replace_visitor_with_tc(ctx), m_old_fns(old_fns), m_ues(ues) {}
    };

    expr operator()(expr const & e) {
        unpack_eqns ues(m_ctx, e);
        buffer<expr> old_fns;
        bool modified = false;
        for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
            expr const & fn = ues.get_fn(fidx);
            old_fns.push_back(fn);
            unsigned arity = ues.get_arity_of(fidx);
            if (arity > 1) {
                expr new_type = pack_as_unary(m_ctx.infer(fn), arity);
                ues.update_fn_type(fidx, new_type);
                modified = true;
            }
        }
        if (!modified) return e;
        update_apps_fn updt(m_ctx, old_fns, ues);
        for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
            buffer<expr> & eqs = ues.get_eqns_of(fidx);
            for (expr & eq : eqs)
                eq = updt(eq);
        }
        expr r = ues.repack();
        lean_trace("eqn_compiler", tout() << "making function(s) unary:\n" << r << "\n";);
        return r;
    }
};

expr pack_domain(type_context_old & ctx, expr const & e) {
    return sigma_packer_fn(ctx)(e);
}
}
