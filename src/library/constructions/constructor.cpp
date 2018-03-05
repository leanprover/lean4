/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/app_builder.h"
#include "library/trace.h"
#include "library/inductive_compiler/ginductive.h"

namespace lean {
optional<expr> mk_constructor_eq_constructor_inconsistency_proof(type_context_old & ctx, expr const & e1, expr const & e2, expr const & h) {
    environment const & env = ctx.env();
    optional<name> c1 = is_gintro_rule_app(env, e1);
    if (!c1) return none_expr();
    optional<name> c2 = is_gintro_rule_app(env, e2);
    if (!c2) return none_expr();
    if (*c1 == *c2) return none_expr();
    expr A = ctx.relaxed_whnf(ctx.infer(e1));
    expr I = get_app_fn(A);
    if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I)))
        return none_expr();
    name nc_name(const_name(I), "no_confusion");
    if (!env.find(nc_name)) return none_expr();
    expr pr = mk_app(ctx, nc_name, {mk_false(), e1, e2, h});
    return some_expr(pr);
}

optional<expr> mk_constructor_ne_constructor_proof(type_context_old & ctx, expr const & e1, expr const & e2) {
    type_context_old::tmp_locals locals(ctx);
    expr h  = locals.push_local("_h", mk_eq(ctx, e1, e2));
    if (optional<expr> pr = mk_constructor_eq_constructor_inconsistency_proof(ctx, e1, e2, h))
        return some_expr(locals.mk_lambda(*pr));
    else
        return none_expr();
}

optional<expr> mk_constructor_eq_constructor_implied_core(type_context_old & ctx, expr const & e1, expr const & e2, expr const & h, buffer<expr_pair> & implied_pairs) {
    // TODO(Leo, Daniel): add support for generalized inductive datatypes
    // TODO(Leo): add a definition for this proof at inductive datatype declaration time?
    environment const & env = ctx.env();
    optional<name> c1 = is_constructor_app(env, e1);
    if (!c1) return none_expr();
    optional<name> c2 = is_constructor_app(env, e2);
    if (!c2) return none_expr();
    if (*c1 != *c2) return none_expr();
    expr A = ctx.relaxed_whnf(ctx.infer(e1));
    expr I = get_app_fn(A);
    if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I)))
        return none_expr();
    name nct_name(const_name(I), "no_confusion_type");
    if (!env.find(nct_name)) return none_expr();
    unsigned num_params  = *inductive::get_num_params(env, const_name(I));
    buffer<expr> e1_args, e2_args;
    get_app_args(e1, e1_args);
    get_app_args(e2, e2_args);
    unsigned cnstr_arity = get_arity(env.get(*c1).get_type());
    if (e1_args.size() != cnstr_arity) return none_expr();
    lean_assert(cnstr_arity >= num_params);
    lean_assert(e1_args.size() == e2_args.size());
    unsigned num_new_eqs = cnstr_arity - num_params;
    /* Collect implied equalities */
    buffer<expr> implied_eqs;
    for (unsigned i = num_params; i < e1_args.size(); i++) {
        expr const & arg1 = e1_args[i];
        expr const & arg2 = e2_args[i];
        implied_pairs.emplace_back(arg1, arg2);
        if (ctx.is_def_eq(ctx.infer(arg1), ctx.infer(arg2)))
            implied_eqs.push_back(mk_eq(ctx, arg1, arg2));
        else
            implied_eqs.push_back(mk_heq(ctx, arg1, arg2));
    }
    /* Construct motive (eq_1 /\ ... /\ eq_n), where eq_i's are the implied equalities */
    if (implied_eqs.empty()) return none_expr();
    expr motive = implied_eqs.back();
    unsigned i  = implied_eqs.size() - 1;
    while (i > 0) {
        --i;
        motive  = mk_and(implied_eqs[i], motive);
    }
    /* Construct proof for (eq_1 /\ ... /\ eq_n) using no_confusion.
       The proof is of the form:
           I.no_confusion motive e1 e2 h (fun eq_1 ... eq_n, and.intro eq_1 ... eq_n) */
    name nc_name(const_name(I), "no_confusion");
    expr result_prefix = mk_app(ctx, nc_name, {motive, e1, e2, h});
    expr nct = ctx.relaxed_whnf(mk_app(ctx, nct_name, motive, e1, e2));
    if (!is_pi(nct)) return none_expr();
    expr it  = binding_domain(nct);
    type_context_old::tmp_locals locals(ctx);
    buffer<expr> eq_proofs;
    for (unsigned i = 0; i < num_new_eqs; i++) {
        /* Remark: some of the hypotheses are heterogeneous, we should convert them
           back into homogeneous. */
        if (!is_pi(it)) return none_expr();
        expr heq = locals.push_local_from_binding(it);
        expr A, B, lhs, rhs;
        if (is_heq(binding_domain(it), A, lhs, B, rhs) && ctx.is_def_eq(A, B)) {
            eq_proofs.push_back(mk_eq_of_heq(ctx, heq));
        } else {
            eq_proofs.push_back(heq);
        }
        it = ctx.relaxed_whnf(instantiate(binding_body(it), heq));
    }
    expr body_pr = eq_proofs.back();
    i = eq_proofs.size() - 1;
    while (i > 0) {
        --i;
        body_pr = mk_and_intro(ctx, eq_proofs[i], body_pr);
    }
    expr fun = locals.mk_lambda(body_pr);
    return some_expr(mk_app(result_prefix, fun));
}

bool mk_constructor_eq_constructor_implied_eqs(type_context_old & ctx, expr const & e1, expr const & e2, expr const & h, buffer<std::tuple<expr, expr, expr>> & result) {
    buffer<expr_pair> implied_pairs;
    optional<expr> conj_pr = mk_constructor_eq_constructor_implied_core(ctx, e1, e2, h, implied_pairs);
    if (!conj_pr) return false;
    expr pr = *conj_pr;
    unsigned sz = implied_pairs.size();
    for (unsigned i = 0; i < sz - 1; i++) {
        result.emplace_back(implied_pairs[i].first, implied_pairs[i].second, mk_and_elim_left(ctx, pr));
        pr = mk_and_elim_right(ctx, pr);
    }
    result.emplace_back(implied_pairs.back().first, implied_pairs.back().second, pr);
    return true;
}
}
