/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/constructions/injective.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "library/util.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/subst_tactic.h"
#include "library/tactic/tactic_evaluator.h"

namespace lean {

static void collect_args(type_context_old & tctx, expr const & type, unsigned num_params,
                  buffer<expr> & params, buffer<expr> & args1, buffer<expr> & args2, buffer<expr> & new_args) {
    expr ty = tctx.relaxed_whnf(type);

    for (unsigned param_idx = 0; param_idx < num_params; ++param_idx) {
        expr param = tctx.push_local(binding_name(ty), binding_domain(ty), mk_implicit_binder_info());
        params.push_back(param);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), param));
    }

    expr type_post_params = ty;

    while (is_pi(ty)) {
        expr arg = tctx.push_local(binding_name(ty), binding_domain(ty), mk_implicit_binder_info());
        args1.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    expr result_type = ty;
    ty = type_post_params;

    for (expr const & arg1 : args1) {
        if (occurs(arg1, result_type)) {
            args2.push_back(arg1);
        } else {
            expr arg2 = tctx.push_local(binding_name(ty), binding_domain(ty), mk_implicit_binder_info());
            args2.push_back(arg2);
            new_args.push_back(arg2);
        }
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), args2.back()));
    }
    lean_assert(args1.size() == args2.size());
    lean_assert(!is_pi(ty));
}

expr mk_injective_type_core(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names, bool use_eq) {
    // The transparency needs to match the kernel since we need to be consistent with the no_confusion construction.
    type_context_old ctx(env, transparency_mode::All);
    buffer<expr> params, args1, args2, new_args;
    collect_args(ctx, ir_type, num_params, params, args1, args2, new_args);
    expr c_ir_params = mk_app(mk_constant(ir_name, param_names_to_levels(lp_names)), params);
    expr lhs = mk_app(c_ir_params, args1);
    expr rhs = mk_app(c_ir_params, args2);
    expr eq_type = mk_eq(ctx, lhs, rhs);

    buffer<expr> eqs;
    for (unsigned arg_idx = 0; arg_idx < args1.size(); ++arg_idx) {
        if (!ctx.is_prop(ctx.infer(args1[arg_idx])) && args1[arg_idx] != args2[arg_idx]) {
            if (ctx.is_def_eq(ctx.infer(args1[arg_idx]), ctx.infer(args2[arg_idx]))) {
                eqs.push_back(mk_eq(ctx, args1[arg_idx], args2[arg_idx]));
            } else {
                eqs.push_back(mk_heq(ctx, args1[arg_idx], args2[arg_idx]));
            }
        }
    }

    expr and_type;
    if (eqs.empty()) {
        and_type = mk_true();
    } else {
        and_type = eqs.back();
        unsigned i = eqs.size() - 1;
        while (i > 0) {
            --i;
            and_type = mk_and(eqs[i], and_type);
        }
    }

    expr result = use_eq ? mk_eq(ctx, eq_type, and_type) : mk_arrow(eq_type, and_type);
    return ctx.mk_pi(params, ctx.mk_pi(args1, ctx.mk_pi(new_args, result)));
}

expr mk_injective_type(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names) {
    return mk_injective_type_core(env, ir_name, ir_type, num_params, lp_names, false);
}

expr mk_injective_eq_type(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names) {
    return mk_injective_type_core(env, ir_name, ir_type, num_params, lp_names, true);
}

expr prove_by_assumption(type_context_old & tctx, expr const & ty, expr const & eq) {
    if (is_eq(ty) && is_heq(tctx.infer(eq))) {
        return mk_eq_of_heq(tctx, eq);
    } else {
        return eq;
    }
}

expr prove_conjuncts_core(type_context_old & tctx, expr const & ty, buffer<expr> const & eqs, unsigned idx) {
    if (idx == eqs.size() - 1) {
        lean_assert(!is_and(ty));
        return prove_by_assumption(tctx, ty, eqs[idx]);
    } else {
        expr A, B;
        lean_verify(is_and(ty, A, B));
        expr a = prove_by_assumption(tctx, A, eqs[idx]);
        expr b = prove_conjuncts_core(tctx, B, eqs, idx+1);
        return mk_app(mk_constant(get_and_intro_name()), {A, B, a, b});
    }
}

expr prove_conjuncts(type_context_old & tctx, expr const & ty, buffer<expr> const & eqs) {
    return prove_conjuncts_core(tctx, ty, eqs, 0);
}

expr prove_injective(environment const & env, expr const & inj_type, name const & ind_name) {
    type_context_old tctx(env);
    expr ty = inj_type;

    buffer<expr> args;
    while (is_pi(ty)) {
        expr arg = tctx.push_local_from_binding(ty);
        args.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    lean_assert(!args.empty());

    expr tgt = ty;

    if (tgt == mk_true())
        return tctx.mk_lambda(args, mk_true_intro());

    expr H_eq = args.back();
    expr A, lhs, rhs;
    lean_verify(is_eq(tctx.infer(H_eq), A, lhs, rhs));

    buffer<expr> nc_args;
    expr A_fn = get_app_args(A, nc_args);
    lean_assert(is_constant(A_fn));

    nc_args.push_back(tgt);
    nc_args.push_back(lhs);
    nc_args.push_back(rhs);
    nc_args.push_back(H_eq);

    expr H_nc = mk_app(mk_constant(name(ind_name, "no_confusion"), cons(mk_level_zero(), const_levels(A_fn))), nc_args);

    // (x1 = x2 -> xs1 == xs2 -> (x1 = x2 /\ xs1 = xs2)
    ty = binding_domain(tctx.relaxed_whnf(tctx.infer(H_nc)));

    buffer<expr> eqs;
    buffer<expr> eqs_to_keep;
    while (is_pi(ty)) {
        expr eq = tctx.push_local_from_binding(ty);
        eqs.push_back(eq);
        expr eq_type = tctx.infer(eq);
        expr lhs, rhs;
        if ((is_eq(eq_type, lhs, rhs) && lhs != rhs) ||
            (is_heq(eq_type, lhs, rhs) && lhs != rhs)) {
            eqs_to_keep.push_back(eq);
        }
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), eq));
    }

    return tctx.mk_lambda(args, mk_app(H_nc, tctx.mk_lambda(eqs, prove_conjuncts(tctx, ty, eqs_to_keep))));
}

expr prove_injective_arrow(environment const & env, expr const & inj_arrow_type, name const & inj_name, level_param_names const & inj_lp_names) {
    type_context_old tctx(env);
    expr ty = inj_arrow_type;

    buffer<expr> args;
    while (is_pi(ty)) {
        expr arg = tctx.push_local_from_binding(ty);
        args.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    lean_assert(args.size() >= 3);
    expr H_eq = args[args.size() - 3];
    expr H_P = args[args.size() - 2];
    expr H_arrow = args[args.size() - 1];

    expr conjuncts = mk_app(mk_constant(inj_name, param_names_to_levels(inj_lp_names)), args.size() - 2, args.begin());
    expr pf = H_arrow;
    while (is_and(tctx.infer(conjuncts))) {
        pf = mk_app(pf, mk_and_elim_left(tctx, conjuncts));
        conjuncts = mk_and_elim_right(tctx, conjuncts);
    }
    pf = mk_app(pf, conjuncts);
    return tctx.mk_lambda(args, pf);
}

environment mk_injective_arrow(environment const & env, name const & ir_name) {
    declaration d = env.get(mk_injective_name(ir_name));
    type_context_old tctx(env);

    name P_lp_name = mk_fresh_lp_name(d.get_univ_params());
    expr P = tctx.push_local(name("P"), mk_sort(mk_param_univ(P_lp_name)), mk_strict_implicit_binder_info());

    expr ty = d.get_type();
    buffer<expr> args;
    while (is_pi(ty)) {
        expr arg = tctx.push_local_from_binding(ty);
        args.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    buffer<expr> eqs;
    expr it = ty;
    expr A, B;
    while (is_and(it, A, B)) {
        eqs.push_back(A);
        it = B;
    }
    eqs.push_back(it);

    expr antecedent = P;
    unsigned i = eqs.size();
    while (i > 0) {
        --i;
        antecedent = mk_arrow(eqs[i], antecedent);
    }

    name inj_arrow_name = mk_injective_arrow_name(ir_name);
    expr inj_arrow_type = tctx.mk_pi(args, tctx.mk_pi(P, mk_arrow(antecedent, P)));
    expr inj_arrow_val = prove_injective_arrow(env, inj_arrow_type, mk_injective_name(ir_name), d.get_univ_params());
    lean_trace(name({"constructions", "injective"}), tout() << inj_arrow_name << " : " << inj_arrow_type << "\n";);
    environment new_env = module::add(env, check(env, mk_definition_inferring_trusted(env, inj_arrow_name,
                                                                                      cons(P_lp_name, d.get_univ_params()), inj_arrow_type, inj_arrow_val, true)));
    return new_env;
}

expr prove_injective_eq(environment const & env, expr const & inj_eq_type, name const & inj_eq_name) {
    try {
        type_context_old ctx(env, transparency_mode::Semireducible);
        expr dummy_ref;
        tactic_state s = mk_tactic_state_for(env, options(), inj_eq_name, metavar_context(), local_context(), inj_eq_type);
        vm_obj r = tactic_evaluator(ctx, options(), dummy_ref)(mk_constant(get_tactic_mk_inj_eq_name()), s);
        if (auto new_s = tactic::is_success(r)) {
            metavar_context mctx = new_s->mctx();
            return mctx.instantiate_mvars(new_s->main());
        }
    } catch (exception & ex) {
        throw nested_exception(sstream() << "failed to generate auxiliary lemma '" << inj_eq_name << "'", ex);
    }
    throw exception(sstream() << "failed to generate auxiliary lemma '" << inj_eq_name << "'");
}

environment mk_injective_lemmas(environment const & _env, name const & ind_name, bool gen_inj_eq) {
    environment env = _env;

    auto idecls = inductive::is_inductive_decl(env, ind_name);
    if (!idecls)
        throw exception(sstream() << "'" << ind_name << "' not an inductive datatype\n");

    if (is_inductive_predicate(env, ind_name) || !can_elim_to_type(env, ind_name))
        return _env;

    inductive::inductive_decl idecl = *idecls;
    level_param_names lp_names = idecl.m_level_params;
    unsigned num_params = idecl.m_num_params;

    buffer<inductive::intro_rule> intro_rules;
    to_buffer(idecl.m_intro_rules, intro_rules);

    for (inductive::intro_rule ir : intro_rules) {
        name ir_name = inductive::intro_rule_name(ir);
        expr ir_type = inductive::intro_rule_type(ir);
        expr inj_type = mk_injective_type(env, ir_name, ir_type, num_params, lp_names);
        expr inj_val = prove_injective(env, inj_type, ind_name);
        lean_trace(name({"constructions", "injective"}), tout() << ir_name << " : " << inj_type << " :=\n  " << inj_val << "\n";);
        env = module::add(env, check(env, mk_definition_inferring_trusted(env, mk_injective_name(ir_name), lp_names, inj_type, inj_val, true)));
        env = mk_injective_arrow(env, ir_name);
        if (gen_inj_eq && env.find(get_tactic_mk_inj_eq_name())) {
            name inj_eq_name  = mk_injective_eq_name(ir_name);
            expr inj_eq_type  = mk_injective_eq_type(env, ir_name, ir_type, num_params, lp_names);
            expr inj_eq_value = prove_injective_eq(env, inj_eq_type, inj_eq_name);
            env = module::add(env, check(env, mk_definition_inferring_trusted(env, inj_eq_name, lp_names, inj_eq_type, inj_eq_value, true)));
        }
    }
    return env;
}

name mk_injective_name(name const & ir_name) {
    return name(ir_name, "inj");
}

name mk_injective_eq_name(name const & ir_name) {
    return name(ir_name, "inj_eq");
}

name mk_injective_arrow_name(name const & ir_name) {
    return name(ir_name, "inj_arrow");
}

void initialize_injective() {
    register_trace_class(name({"constructions", "injective"}));
}

void finalize_injective() {}
}
