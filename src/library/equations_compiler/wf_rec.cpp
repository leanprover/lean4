/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/type_context.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/app_builder.h"
#include "library/sorry.h" // remove after we add tactic for proving recursive calls are decreasing
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/pack_domain.h"
#include "library/equations_compiler/pack_mutual.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/util.h"

namespace lean {
#define trace_wf(Code) lean_trace(name({"eqn_compiler", "wf_rec"}), type_context ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)

#define trace_debug_wf(Code) lean_trace(name({"debug", "eqn_compiler", "wf_rec"}), type_context ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)

struct wf_rec_fn {
    environment      m_env;
    options          m_opts;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;

    expr             m_R;
    expr             m_R_wf;

    wf_rec_fn(environment const & env, options const & opts,
              metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_opts(opts), m_mctx(mctx), m_lctx(lctx) {
    }

    type_context mk_type_context(local_context const & lctx) {
        return type_context(m_env, m_opts, m_mctx, lctx, transparency_mode::Semireducible);
    }

    type_context mk_type_context() {
        return mk_type_context(m_lctx);
    }

    expr pack_domain(expr const & eqns) {
        type_context ctx = mk_type_context();
        expr r = ::lean::pack_domain(ctx, eqns);
        m_env  = ctx.env();
        m_mctx = ctx.mctx();
        return r;
    }

    expr pack_mutual(expr const & eqns) {
        type_context ctx = mk_type_context();
        expr r = ::lean::pack_mutual(ctx, eqns);
        m_env  = ctx.env();
        m_mctx = ctx.mctx();
        return r;
    }

    expr_pair mk_wf_relation(expr const & eqns) {
        lean_assert(get_equations_header(eqns).m_num_fns == 1);
        type_context ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        try {
            expr fn_type = ctx.relaxed_whnf(ctx.infer(ues.get_fn(0)));
            lean_assert(is_pi(fn_type));
            expr d       = binding_domain(fn_type);
            expr wf      = mk_app(ctx, get_has_well_founded_name(), d);
            if (auto inst = ctx.mk_class_instance(wf)) {
                bool mask[2] = {true, true};
                expr args[2] = {d, *inst};
                expr r   = mk_app(ctx, get_has_well_founded_r_name(), 2, mask, args);
                expr wf  = mk_app(ctx, get_has_well_founded_wf_name(), 2, mask, args);
                return expr_pair(r, wf);
            }
        } catch (exception & ex) {
            throw nested_exception(some_expr(m_ref),
                                   "failed to create well founded relation using type class resolution",
                                   ex);
        }
        throw generic_exception(m_ref, "failed to create well founded relation using type class resolution");
    }


    /* Return the type of the functional. */
    expr mk_new_fn_type(type_context & ctx, unpack_eqns const & ues) {
        type_context::tmp_locals locals(ctx);
        expr fn        = ues.get_fn(0);
        expr fn_type   = ctx.relaxed_whnf(ctx.infer(fn));
        lean_assert(ues.get_arity_of(0) == 1);
        expr x         = locals.push_local("_x", binding_domain(fn_type));
        expr y         = locals.push_local("_y", binding_domain(fn_type));
        expr hlt       = mk_app(m_R, y, x);
        expr Cy        = instantiate(binding_body(fn_type), y);
        expr F_type    = ctx.mk_pi(y, mk_arrow(hlt, Cy));
        expr F         = locals.push_local("_F", F_type);
        expr Cx        = instantiate(binding_body(fn_type), x);
        return ctx.mk_pi(x, ctx.mk_pi(F, Cx));
    }

    struct elim_rec_apps_fn : public replace_visitor_with_tc {
        expr    m_fn;
        expr    m_R;
        expr    m_x;
        expr    m_F;

        elim_rec_apps_fn(type_context & ctx, expr const & fn, expr const & R, expr const & x, expr const & F):
            replace_visitor_with_tc(ctx), m_fn(fn), m_R(R), m_x(x), m_F(F) {}

        virtual expr visit_local(expr const & e) {
            if (mlocal_name(e) == mlocal_name(m_fn)) {
                /* unexpected occurrence of recursive function */
                throw generic_exception(e, "unexpected occurrence of recursive function\n");
            }
            return e;
        }

        /* Prove that y < x */
        expr mk_dec_proof(expr const & y) {
            expr y_R_x = mk_app(m_R, y, m_x);
            // TODO(Leo): invoke tactic, we use sorry for now
            return mk_sorry(y_R_x);
        }

        virtual expr visit_app(expr const & e) {
            expr const & fn = app_fn(e);
            if (is_local(fn) && mlocal_name(fn) == mlocal_name(m_fn)) {
                expr y   = visit(app_arg(e));
                expr hlt = mk_dec_proof(y);
                return mk_app(m_F, y, hlt);
            } else {
                return replace_visitor_with_tc::visit_app(e);
            }
        }
    };

    void update_eqs(type_context & ctx, unpack_eqns & ues, expr const & fn, expr const & new_fn) {
        buffer<expr> & eqns = ues.get_eqns_of(0);
        buffer<expr> new_eqns;
        for (expr const & eqn : eqns) {
            unpack_eqn ue(ctx, eqn);
            expr lhs = ue.lhs();
            expr rhs = ue.rhs();
            buffer<expr> lhs_args;
            get_app_args(lhs, lhs_args);
            lean_assert(lhs_args.size() == 1);
            expr new_lhs = mk_app(new_fn, lhs_args);
            expr type    = ctx.whnf(ctx.infer(new_lhs));
            lean_assert(is_pi(type));
            ue.lhs()     = new_lhs;
            type_context::tmp_locals locals(ctx);
            expr F       = locals.push_local_from_binding(type);
            ue.rhs()     = ctx.mk_lambda(F, elim_rec_apps_fn(ctx, fn, m_R, lhs_args[0], F)(rhs));
            new_eqns.push_back(ue.repack());
        }
        eqns = new_eqns;
    }

    expr elim_recursion(expr const & eqns) {
        type_context ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        lean_assert(ues.get_num_fns() == 1);
        expr fn      = ues.get_fn(0);
        expr fn_type = ctx.infer(fn);

        expr new_fn_type = mk_new_fn_type(ctx, ues);
        trace_debug_wf(tout() << "\n"; tout() << "new function type: " << new_fn_type << "\n";);
        expr new_fn      = ues.update_fn_type(0, new_fn_type);
        update_eqs(ctx, ues, fn, new_fn);
        expr new_eqns    = ues.repack();
        trace_debug_wf(tout() << "after well_founded elim_recursion:\n" << new_eqns << "\n";);
        m_mctx = ctx.mctx();
        return new_eqns;
    }

    expr mk_fix(expr const & aux_fn) {
        type_context ctx = mk_type_context();
        type_context::tmp_locals locals(ctx);
        buffer<expr> fn_args;
        expr it   = ctx.relaxed_whnf(ctx.infer(aux_fn));
        lean_assert(is_pi(it));
        expr x_ty = binding_domain(it);
        expr x    = locals.push_local("_x", x_ty);
        it        = ctx.relaxed_whnf(instantiate(binding_body(it), x));
        lean_assert(is_pi(it));
        expr Cx   = binding_body(it);
        lean_assert(closed(it));
        expr C    = ctx.mk_lambda(x, Cx);
        level u_1 = get_level(ctx, x_ty);
        level u_2 = get_level(ctx, Cx);
        expr fix  = mk_app({mk_constant(get_well_founded_fix_name(), {u_1, u_2}), x_ty, C, m_R, m_R_wf, aux_fn, x});
        return ctx.mk_lambda(x, fix);
    }

    expr operator()(expr eqns) {
        m_ref    = eqns;
        m_header = get_equations_header(eqns);
        /* Make sure all functions are unary */
        eqns     = pack_domain(eqns);
        trace_debug_wf(tout() << "after pack_domain\n" << eqns << "\n";);

        /* Make sure we have only one function */
        equations_header const & header = get_equations_header(eqns);
        if (header.m_num_fns > 1) {
            eqns = pack_mutual(eqns);
        }

        /* Retrieve well founded relation */
        if (is_wf_equations(eqns)) {
            m_R    = equations_wf_rel(eqns);
            m_R_wf = equations_wf_proof(eqns);
        } else {
            std::tie(m_R, m_R_wf) = mk_wf_relation(eqns);
        }
        {
            lean_trace_init_bool(name({"eqn_compiler", "wf_rec"}), get_pp_implicit_name(), true);
            trace_wf(tout() << "using well_founded relation\n" << m_R << " :\n  "
                     << mk_type_context().infer(m_R) << "\n";);
        }

        /* Eliminate recursion using functional. */
        eqns = elim_recursion(eqns);
        trace_debug_wf(tout() << "after elim_recursion\n" << eqns << "\n";);

        /* Eliminate pattern matching */
        elim_match_result r = elim_match(m_env, m_opts, m_mctx, m_lctx, eqns);
        expr fn = mk_fix(r.m_fn);

        trace_debug_wf(tout() << "after mk_fix\n" << fn << " :\n  " << mk_type_context().infer(fn) << "\n";);

        // TODO(Leo):
        throw exception("support for well-founded recursion has not been implemented yet, "
                        "use 'set_option trace.eqn_compiler true' for additional information");
    }
};

/** \brief (Try to) eliminate "recursive calls" in the equations \c eqns by using well founded recursion.
    If successful, elim_match is used to compile pattern matching. */
expr wf_rec(environment & env, options const & opts,
            metavar_context & mctx, local_context const & lctx,
            expr const & eqns) {
    wf_rec_fn proc(env, opts, mctx, lctx);
    expr r = proc(eqns);
    env    = proc.m_env;
    mctx   = proc.m_mctx;
    return r;
}

void initialize_wf_rec() {
    register_trace_class({"eqn_compiler", "wf_rec"});
    register_trace_class({"debug", "eqn_compiler", "wf_rec"});
}

void finalize_wf_rec() {
}
}
