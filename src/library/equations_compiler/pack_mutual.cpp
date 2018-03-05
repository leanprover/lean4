/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/private.h"
#include "library/app_builder.h"
#include "library/type_context.h"
#include "library/locals.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"

namespace lean {
#define trace_debug_mutual(Code) lean_trace(name({"debug", "eqn_compiler", "mutual"}), scope_trace_env _scope(m_ctx.env(), m_ctx); Code)

static expr mk_mutual_arg(type_context_old & ctx, expr const & e, unsigned fidx, unsigned num_fns,
                          expr psum_type, unsigned i) {
    if (i == num_fns - 1) {
        return e;
    } else {
        psum_type = ctx.relaxed_whnf(psum_type);
        buffer<expr> args;
        get_app_args(psum_type, args);
        lean_assert(args.size() == 2);
        if (i == fidx) {
            return mk_app(ctx, get_psum_inl_name(), args[0], args[1], e);
        } else {
            expr r = mk_mutual_arg(ctx, e, fidx, num_fns, args[1], i+1);
            return mk_app(ctx, get_psum_inr_name(), args[0], args[1], r);
        }
    }
}

expr mk_mutual_arg(type_context_old & ctx, expr const & e, unsigned fidx, unsigned num_fns, expr const & psum_type) {
    return mk_mutual_arg(ctx, e, fidx, num_fns, psum_type, 0);
}

struct pack_mutual_fn {
    type_context_old & m_ctx;

    pack_mutual_fn(type_context_old & ctx):m_ctx(ctx) {}

    expr mk_new_domain(buffer<expr> const & domains) {
        unsigned i = domains.size();
        lean_assert(i > 1);
        --i;
        expr r = domains[i];
        while (i > 0) {
            --i;
            r = mk_app(m_ctx, get_psum_name(), domains[i], r);
        }
        return r;
    }

    expr mk_new_codomain(expr const & x, unsigned i, buffer<expr> const & codomains, level codomains_lvl) {
        if (i == codomains.size() - 1) {
            return instantiate(codomains[i], x);
        } else {
            expr x_type = m_ctx.relaxed_whnf(m_ctx.infer(x));
            buffer<expr> args;
            expr psum = get_app_args(x_type, args);
            lean_assert(const_name(psum) == get_psum_name());
            lean_assert(args.size() == 2);
            levels psum_cases_on_lvls(mk_succ(codomains_lvl), const_levels(psum));
            expr cases_on = mk_constant(get_psum_cases_on_name(), psum_cases_on_lvls);
            /* Add parameters */
            cases_on = mk_app(cases_on, args);
            /* Add motive */
            expr motive = mk_sort(codomains_lvl);
            cases_on = mk_app(cases_on, m_ctx.mk_lambda(x, motive));
            /* Add major */
            cases_on = mk_app(cases_on, x);
            /* Add minors */
            type_context_old::tmp_locals locals(m_ctx);
            expr y_1 = locals.push_local("_s", args[0]);
            expr m_1 = m_ctx.mk_lambda(y_1, instantiate(codomains[i], y_1));
            expr y_2 = locals.push_local("_s", args[1]);
            expr m_2 = mk_new_codomain(y_2, i+1, codomains, codomains_lvl);
            m_2      = m_ctx.mk_lambda(y_2, m_2);
            return mk_app(cases_on, m_1, m_2);
        }
    }

    struct replace_fns : public replace_visitor_with_tc {
        unpack_eqns const & m_ues;
        expr                m_new_fn;
        expr                m_new_domain;

        replace_fns(type_context_old & ctx, unpack_eqns const & ues, expr const & new_fn):
            replace_visitor_with_tc(ctx),
            m_ues(ues),
            m_new_fn(new_fn) {
            expr new_fn_type = m_ctx.relaxed_whnf(m_ctx.infer(m_new_fn));
            lean_assert(is_pi(new_fn_type));
            m_new_domain     = m_ctx.relaxed_whnf(binding_domain(new_fn_type));
            lean_assert(is_constant(get_app_fn(m_new_domain)), get_psum_name());
        }

        optional<unsigned> get_fidx(expr const & fn) const {
            if (!is_local(fn))
                return optional<unsigned>();
            for (unsigned fidx = 0; fidx < m_ues.get_num_fns(); fidx++) {
                if (mlocal_name(m_ues.get_fn(fidx)) == mlocal_name(fn))
                    return optional<unsigned>(fidx);
            }
            return optional<unsigned>();
        }

        expr mk_new_arg(expr const & e, unsigned fidx) {
            return mk_mutual_arg(m_ctx, e, fidx, m_ues.get_num_fns(), m_new_domain);
        }

        virtual expr visit_app(expr const & e) override {
            if (optional<unsigned> fidx = get_fidx(app_fn(e))) {
                expr arg = visit(app_arg(e));
                expr new_arg = mk_new_arg(arg, *fidx);
                return copy_tag(e, mk_app(m_new_fn, new_arg));
            } else {
                return replace_visitor::visit_app(e);
            }
        }

        virtual expr visit_local(expr const & e) override {
            if (get_fidx(e)) {
                throw generic_exception(e, "unexpected occurrence of recursive function\n");
            } else {
                return e;
            }
        }
    };

    expr operator()(expr const & e) {
        unpack_eqns ues(m_ctx, e);
        if (ues.get_num_fns() == 1)
            return e;
        /* Given
              f_1 : Pi (x : A_1), B_1 x
              ...
              f_n : Pi (x : A_n), B_n x

           create a function with type
              f   : Pi (x : psum A_1 ... (psum A_{n-1} A_n)), psum.cases_on x (fun y, B_1 y) (... (fun y, B_n y) ...)

           remark: this module assumes the B_i's are in the same universe. */
        type_context_old::tmp_locals locals(m_ctx);
        buffer<expr> domains;
        buffer<expr> codomains;
        level        codomains_lvl;
        equations_header header = get_equations_header(e);
        name         new_fn_name;
        name         new_fn_actual_name;
        if (header.m_is_private) {
            new_fn_actual_name = *get_private_prefix(m_ctx.env(), head(header.m_fn_actual_names));
        }
        for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
            expr const & fn = ues.get_fn(fidx);
            new_fn_name        = new_fn_name + mlocal_pp_name(fn);
            new_fn_actual_name = new_fn_actual_name + mlocal_pp_name(fn);
            lean_assert(ues.get_arity_of(fidx) == 1);
            expr fn_type       = m_ctx.relaxed_whnf(m_ctx.infer(fn));
            lean_assert(is_pi(fn_type));
            domains.push_back(binding_domain(fn_type));
            expr y             = locals.push_local("_s", binding_domain(fn_type));
            expr c             = instantiate(binding_body(fn_type), y);
            level c_lvl        = get_level(m_ctx, c);
            if (fidx == 0) {
                codomains_lvl = c_lvl;
            } else if (!m_ctx.is_def_eq(mk_sort(c_lvl), mk_sort(codomains_lvl))) {
                throw generic_exception(e, "invalid mutual definition, result types must be in the same universe");
            }
            codomains.push_back(binding_body(fn_type));
        }

        new_fn_name = name(new_fn_name, "_mutual");
        new_fn_actual_name = name(new_fn_actual_name, "_mutual");

        expr new_domain   = mk_new_domain(domains);
        expr x            = locals.push_local("_x", new_domain);
        expr new_codomain = mk_new_codomain(x, 0, codomains, codomains_lvl);
        expr new_fn_type  = m_ctx.mk_pi(x, new_codomain);
        expr new_fn       = locals.push_local(new_fn_name, new_fn_type, mk_rec_info(true));

        trace_debug_mutual(tout() << "new function " << new_fn_name << " : " << new_fn_type << "\n";);

        equations_header new_header = get_equations_header(e);
        new_header.m_fn_names         = to_list(new_fn_name);
        new_header.m_fn_actual_names  = to_list(new_fn_actual_name);
        new_header.m_num_fns          = 1;

        replace_fns replacer(m_ctx, ues, new_fn);

        buffer<expr> new_eqns;
        for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
            buffer<expr> const & eqns = ues.get_eqns_of(fidx);
            for (expr const & eqn : eqns) {
                unpack_eqn ue(m_ctx, eqn);
                expr new_lhs = replacer(ue.lhs());
                expr new_rhs = replacer(ue.rhs());
                expr new_eqn = mk_equation(new_lhs, new_rhs, ue.ignore_if_unused());
                new_eqns.push_back(m_ctx.mk_lambda(new_fn, m_ctx.mk_lambda(ue.get_vars(), new_eqn)));
            }
        }

        expr result;
        if (is_wf_equations(e))
            result = mk_equations(new_header, new_eqns.size(), new_eqns.data(), equations_wf_tactics(e));
        else
            result = mk_equations(new_header, new_eqns.size(), new_eqns.data());

        trace_debug_mutual(tout() << "result\n" << result << "\n";);

        return result;
    }
};

expr pack_mutual(type_context_old & ctx, expr const & e) {
    return pack_mutual_fn(ctx)(e);
}

void initialize_pack_mutual() {
    register_trace_class({"debug", "eqn_compiler", "mutual"});
}

void finalize_pack_mutual() {
}
}
