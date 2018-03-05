/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/app_builder.h"
#include "library/trace.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
static void add_minors(type_context_old & ctx, unsigned nminors, expr & cases, buffer<expr> & new_goals) {
    expr cases_type           = ctx.infer(cases);
    for (unsigned i = 0; i < nminors; i++) {
        cases_type            = ctx.relaxed_whnf(cases_type);
        if (!is_pi(cases_type))
            throw exception("destruct tactic failed, ill-formed inductive datatype");
        expr new_type         = annotated_head_beta_reduce(binding_domain(cases_type));
        expr new_M            = ctx.mk_metavar_decl(ctx.lctx(), new_type);
        new_goals.push_back(new_M);
        cases                 = mk_app(cases, new_M);
        cases_type            = binding_body(cases_type);
    }
}

tactic_state destruct(transparency_mode md, expr const & e, tactic_state const & s) {
    if (!s.goals())
        throw exception("destruct tactic failed, there are no goals to be solved");

    type_context_old ctx          = mk_type_context_for(s, md);
    environment const & env   = ctx.env();
    expr target               = s.get_main_goal_decl()->get_type();
    level target_lvl          = get_level(ctx, target);

    expr e_type               = ctx.relaxed_whnf(ctx.infer(e));
    buffer<expr> I_args;
    expr const & I            = get_app_args(e_type, I_args);
    if (!is_constant(I) ||
        !inductive::is_inductive_decl(env, const_name(I)) ||
        !env.find(name{const_name(I), "cases_on"}))
        throw exception("destruct tactic failed, type of given expression is not an inductive datatype");

    name const & I_name       = const_name(I);
    levels const I_lvls       = const_levels(I);
    bool dep_elim             = inductive::has_dep_elim(env, I_name);
    unsigned nindices         = *inductive::get_num_indices(env, I_name);
    unsigned nparams          = *inductive::get_num_params(env, I_name);
    unsigned nminors          = *inductive::get_num_intro_rules(env, I_name);
    declaration I_decl        = env.get(I_name);
    declaration cases_on_decl = env.get({I_name, "cases_on"});

    if (I_args.size() != nindices + nparams)
        throw exception("destruct tactic failed, ill-formed inductive datatype");

    expr cases;
    levels lvls;
    if (env.get(name(I_name, "rec")).get_num_univ_params() != length(I_lvls)) {
        lvls = cons(target_lvl, I_lvls);
    } else {
        if (!is_zero(target_lvl)) {
            throw exception(sstream() << "destruct tactic failed, recursor '" << cases_on_decl.get_name()
                            << "' can only eliminate into Prop");
        }
        lvls = I_lvls;
    }

    /* cases will contain the cases_on application that we will assing to the main goal */
    cases                     = mk_constant(cases_on_decl.get_name(), lvls);
    /* add params */
    cases                     = mk_app(cases, I_args.size() - nindices, I_args.data());
    buffer<expr> new_goals;
    if (dep_elim) {
        /* add motive */
        buffer<expr> refls; /* refl proof for indices and major */
        {
            type_context_old::tmp_locals locals(ctx);
            buffer<expr> js;
            buffer<expr> eqs;
            expr I_A              = mk_app(I, I_args.size() - nindices, I_args.data());
            expr I_A_type         = ctx.infer(I_A);
            if (nindices > 0) {
                for (unsigned idx = 0; idx < nindices; idx++) {
                    I_A_type      = ctx.relaxed_whnf(I_A_type);
                    if (!is_pi(I_A_type))
                        throw exception("destruct tactic failed, ill-formed inductive datatype");
                    expr j        = locals.push_local_from_binding(I_A_type);
                    js.push_back(j);
                    expr i        = I_args[nparams + idx];
                    if (ctx.is_def_eq(ctx.infer(j), ctx.infer(i))) {
                        eqs.push_back(mk_eq(ctx, i, j));
                        refls.push_back(mk_eq_refl(ctx, i));
                    } else {
                        eqs.push_back(mk_heq(ctx, i, j));
                        refls.push_back(mk_heq_refl(ctx, i));
                    }
                    I_A_type      = instantiate(binding_body(I_A_type), j);
                }
            }
            expr motive           = target;
            expr w                = locals.push_local("w", mk_app(I_A, js));
            if (ctx.is_def_eq(ctx.infer(w), e_type)) {
                motive            = mk_arrow(mk_eq(ctx, e, w), motive);
                refls.push_back(mk_eq_refl(ctx, e));
            } else {
                motive            = mk_arrow(mk_heq(ctx, e, w), motive);
                refls.push_back(mk_heq_refl(ctx, e));
            }
            unsigned i = eqs.size();
            while (i > 0) {
                --i;
                motive            = mk_arrow(eqs[i], motive);
            }
            motive                = locals.mk_lambda(motive);
            cases                 = mk_app(cases, motive);
        }
        /* add indices */
        cases                     = mk_app(cases, nindices, I_args.data() + nparams);
        /* add major */
        cases                     = mk_app(cases, e);
        /* add minors */
        add_minors(ctx, nminors, cases, new_goals);
        /* add refl proofs for indices */
        cases                     = mk_app(cases, refls);
    } else {
        lean_assert(!dep_elim);
        /* add motive */
        {
            type_context_old::tmp_locals locals(ctx);
            if (nindices > 0) {
                expr I_A          = mk_app(I, I_args.size() - nindices, I_args.data());
                expr I_A_type     = ctx.infer(I_A);
                for (unsigned idx = 0; idx < nindices; idx++) {
                    I_A_type      = ctx.relaxed_whnf(I_A_type);
                    if (!is_pi(I_A_type))
                        throw exception("destruct tactic failed, ill-formed inductive datatype");
                    expr j        = locals.push_local_from_binding(I_A_type);
                    I_A_type      = instantiate(binding_body(I_A_type), j);
                }
            }
            expr motive           = target;
            motive                = locals.mk_lambda(motive);
            cases                 = mk_app(cases, motive);
        }
        /* add indices */
        cases                     = mk_app(cases, nindices, I_args.data() + nparams);
        /* add major */
        cases                     = mk_app(cases, e);
        /* add minors */
        add_minors(ctx, nminors, cases, new_goals);
    }
    /* create new tactic state */
    expr g                    = head(s.goals());
    list<expr> gs             = tail(s.goals());
    metavar_context mctx      = ctx.mctx();
    mctx.assign(g, cases);
    return set_mctx_goals(s, mctx, to_list(new_goals.begin(), new_goals.end(), gs));
}

vm_obj tactic_destruct(vm_obj const & e, vm_obj const & md, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    try {
        if (!s.goals()) return mk_no_goals_exception(s);
        tactic_state new_s = destruct(to_transparency_mode(md), to_expr(e), s);
        return tactic::mk_success(new_s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_destruct_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "destruct"}), tactic_destruct);
}

void finalize_destruct_tactic() {
}
}
