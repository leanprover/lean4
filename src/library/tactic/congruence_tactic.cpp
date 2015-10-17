/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/class_instance_resolution.h"
#include "library/tactic/util.h"
#include "library/tactic/intros_tactic.h"
#include "library/tactic/subst_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
enum class congr_arg_kind { Fixed, Singleton, Eq };

optional<expr> mk_congr_subsingleton_thm(type_checker & tc, io_state const & ios, expr const & fn, optional<unsigned> const & expected_num_args,
                                         buffer<congr_arg_kind> & arg_kinds, constraint_seq & cs) {
    expr fn_type = tc.infer(fn, cs);
    buffer<expr> hyps;
    collected_locals ctx_buffer;
    collect_locals(fn_type, ctx_buffer);
    collect_locals(fn, ctx_buffer);
    hyps.append(ctx_buffer.get_collected());
    list<expr> ctx = to_list(hyps);

    buffer<expr> domain;
    expr codomain = to_telescope(tc, fn_type, domain, optional<binder_info>(), cs);
    if (expected_num_args && *expected_num_args != domain.size()) {
        if (*expected_num_args > domain.size())
            return none_expr();
        lean_assert(*expected_num_args < domain.size());
        while (domain.size() > *expected_num_args) {
            codomain = Pi(domain.back(), codomain);
            domain.pop_back();
        }
    }

    buffer<bool> prop;   // pp[i] iff i-th arg is a proposition
    buffer<bool> ss;     // ss[i] is not none iff i-th arg is a subsingleton
    buffer<bool> codomain_deps_on; // codomain_deps_on[i] iff codomain depends on i-th argument
    for (expr const & d : domain) {
        prop.push_back(tc.is_prop(mlocal_type(d), cs) && tc.env().prop_proof_irrel());
        if (prop.back()) {
            ss.push_back(true);
        } else {
            ss.push_back(static_cast<bool>(mk_subsingleton_instance(tc, ios, ctx, mlocal_type(d))));
        }
        codomain_deps_on.push_back(depends_on(codomain, d));
        ctx = cons(d, ctx);
    }

    buffer<expr> new_domain;
    buffer<expr> conclusion_lhs;
    for (unsigned i = 0; i < domain.size(); i++) {
        lean_assert(i == new_domain.size());
        expr const & d_i = domain[i];
        expr new_type    = replace_locals(mlocal_type(d_i), i, domain.data(), new_domain.data());
        expr new_d_i     = mk_local(get_unused_name(local_pp_name(d_i), hyps), new_type);
        hyps.push_back(new_d_i);
        conclusion_lhs.push_back(new_d_i);
        new_domain.push_back(new_d_i);
    }

    buffer<expr> lhss, rhss;
    buffer<optional<expr>> eqs;
    buffer<bool> ss_elim; // true if equality proof should be synthesized using singletion elimination
    buffer<expr> conclusion_rhs;
    name h("he");
    unsigned eqidx = 1;
    for (unsigned i = 0; i < new_domain.size(); i++) {
        expr const & d_i = new_domain[i];
        if (ss[i]) {
            arg_kinds.push_back(congr_arg_kind::Singleton);
            expr new_type = replace_locals(mlocal_type(d_i), rhss, lhss);
            expr new_d_i  = mk_local(get_unused_name(name(local_pp_name(d_i), "new"), hyps), new_type);
            hyps.push_back(new_d_i);
            rhss.push_back(d_i);
            lhss.push_back(new_d_i);
            conclusion_rhs.push_back(new_d_i);
            ss_elim.push_back(!prop[i]);
            eqs.push_back(none_expr());
        } else {
            unsigned j = i+1;
            for (; j < new_domain.size(); j++) {
                expr t_j = mlocal_type(new_domain[j]);
                if (depends_on(t_j, d_i) && !ss[j])
                    break;
            }
            if (j < new_domain.size() || codomain_deps_on[i]) {
                arg_kinds.push_back(congr_arg_kind::Fixed);
                conclusion_rhs.push_back(d_i);
            } else {
                arg_kinds.push_back(congr_arg_kind::Eq);
                expr new_type   = replace_locals(mlocal_type(d_i), rhss, lhss);
                expr new_d_i    = mk_local(get_unused_name(name(local_pp_name(d_i), "new"), hyps), new_type);
                name new_h_name = get_unused_name(name(h, eqidx), hyps);
                eqidx++;
                expr new_eq     = mk_local(new_h_name, mk_eq(tc, new_d_i, d_i));
                hyps.push_back(new_d_i);
                rhss.push_back(d_i);
                lhss.push_back(new_d_i);
                conclusion_rhs.push_back(new_d_i);
                ss_elim.push_back(false);
                eqs.push_back(some_expr(new_eq));
            }
        }
    }
    for (optional<expr> const & eq : eqs) {
        if (eq)
            hyps.push_back(*eq);
    }
    expr conclusion = mk_eq(tc, mk_app(fn, conclusion_lhs), mk_app(fn, conclusion_rhs));
    expr mvar_type  = Pi(hyps, conclusion);
    expr mvar       = mk_metavar(tc.mk_fresh_name(), mvar_type);
    expr meta       = mk_app(mvar, hyps);
    proof_state ps  = to_proof_state(meta, conclusion, tc.mk_ngen()).update_report_failure(false);
    for (unsigned i = 0; i < eqs.size(); i++) {
        goal const & g = head(ps.get_goals());
        optional<expr> const & eq = eqs[i];
        if (eq) {
            auto new_eq = g.find_hyp(local_pp_name(*eq));
            if (auto new_ps = subst(tc.env(), mlocal_name(new_eq->first), false, ps)) {
                ps = *new_ps;
            } else {
                return none_expr();
            }
        } else if (ss_elim[i]) {
            expr lhs       = lhss[i];
            expr rhs       = rhss[i];
            expr new_lhs, new_rhs;
            if (auto it = g.find_hyp(local_pp_name(lhs)))
                new_lhs = it->first;
            else
                return none_expr();
            if (auto it = g.find_hyp(local_pp_name(rhs)))
                new_rhs = it->first;
            else
                return none_expr();
            buffer<expr> hyps;
            g.get_hyps(hyps);
            auto spr = mk_subsingleton_instance(tc, ios, to_list(hyps), mlocal_type(new_lhs));
            if (!spr)
                return none_expr();
            expr new_eq    = mk_local(get_unused_name(name(h, eqidx), hyps), mk_eq(tc, new_rhs, new_lhs));
            eqidx++;
            expr new_eq_pr      = mk_subsingleton_elim(tc, *spr, new_rhs, new_lhs);
            expr aux_mvar       = mk_metavar(tc.mk_fresh_name(), Pi(hyps, g.get_type()));
            expr aux_meta_core  = mk_app(aux_mvar, hyps);
            goal aux_g(mk_app(aux_meta_core, new_eq), g.get_type());
            substitution new_subst = ps.get_subst();
            assign(new_subst, g, mk_app(aux_meta_core, new_eq_pr));
            proof_state aux_ps  = proof_state(ps, goals(aux_g), new_subst);
            if (auto new_ps = subst(tc.env(), mlocal_name(new_eq), false, aux_ps)) {
                ps = *new_ps;
            } else {
                return none_expr();
            }
        } else {
            // do nothing, it is a proposition
        }
    }

    substitution subst = ps.get_subst();
    goal const & g = head(ps.get_goals());
    assign(subst, g, mk_refl(tc, app_arg(g.get_type())));
    expr result    = subst.instantiate_all(mvar);
    try {
        check_term(tc, result);
    } catch (exception &) {
        return none_expr();
    }
    for (expr const & ctx_local : ctx_buffer.get_collected()) {
        result    = mk_app(result, ctx_local);
        mvar_type = instantiate(binding_body(mvar_type), ctx_local);
    }
    result = head_beta_reduce(result);
    return some_expr(result);
}

tactic congruence_tactic() {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) -> optional<proof_state> {
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return none_proof_state();
        }
        goal const & g      = head(gs);
        expr t              = g.get_type();
        substitution subst  = s.get_subst();
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child());
        constraint_seq cs;
        t = tc->whnf(t, cs);
        expr lhs, rhs;
        if (!is_eq(t, lhs, rhs)) {
            throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, goal is not an equality");
            return none_proof_state();
        }

        if (!is_app(lhs) || !is_app(rhs)) {
            throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, left and right hand side of equation must be a function application");
            return none_proof_state();
        }

        buffer<expr> lhs_args, rhs_args;
        expr lhs_fn = get_app_args(lhs, lhs_args);
        expr rhs_fn = get_app_args(rhs, rhs_args);

        if (lhs_args.size() != rhs_args.size()) {
            throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, left and right hand side of equation must have the same number of arguments");
            return none_proof_state();
        }

        expr lhs_fn_type = tc->whnf(tc->infer(lhs_fn, cs), cs);
        expr rhs_fn_type = tc->whnf(tc->infer(rhs_fn, cs), cs);
        if (!tc->is_def_eq(lhs_fn_type, rhs_fn_type, justification(), cs)) {
            throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, functions do not have the same type");
            return none_proof_state();
        }

        buffer<goal> new_goals;
        optional<expr> fn_pr;
        if (!tc->is_def_eq(lhs_fn, rhs_fn, justification(), cs)) {
            expr new_type = mk_eq(*tc, lhs_fn, rhs_fn);
            expr new_meta = g.mk_meta(ngen.next(), new_type);
            new_goals.push_back(goal(new_meta, new_type));
            fn_pr = new_meta;
        }

        buffer<congr_arg_kind> arg_kinds;
        auto cg_proof = mk_congr_subsingleton_thm(*tc, ios, lhs_fn, some(lhs_args.size()), arg_kinds, cs);
        if (!cg_proof) {
            throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, tactic does not support this kind of dependent function");
            return none_proof_state();
        }

        expr pr = mk_app(*cg_proof, lhs_args);
        for (unsigned i = 0; i < arg_kinds.size(); i++) {
            if (arg_kinds[i] == congr_arg_kind::Fixed) {
                if (!tc->is_def_eq(lhs_args[i], rhs_args[i], justification(), cs)) {
                    throw_tactic_exception_if_enabled(s, sstream() << "invalid 'congruence' tactic, argument #" << (i+1)
                                                      << " must be the same in the left and right hand sides");
                    return none_proof_state();
                }
            } else {
                pr = mk_app(pr, rhs_args[i]);
            }
        }

        for (unsigned i = 0; i < arg_kinds.size(); i++) {
            if (arg_kinds[i] == congr_arg_kind::Eq) {
                if (tc->is_def_eq(lhs_args[i], rhs_args[i], justification(), cs)) {
                    pr = mk_app(pr, mk_refl(*tc, lhs_args[i]));
                } else {
                    expr new_type = mk_eq(*tc, lhs_args[i], rhs_args[i]);
                    expr new_meta = g.mk_meta(ngen.next(), new_type);
                    new_goals.push_back(goal(new_meta, new_type));
                    pr = mk_app(pr, mk_symm(*tc, new_meta));
                }
            }
        }

        if (fn_pr) {
            expr motive_rhs = mk_app(mk_var(0), rhs_args);
            expr motive     = mk_lambda("f", lhs_fn_type, mk_app(app_fn(app_fn(g.get_type())), lhs, motive_rhs));
            pr = mk_subst(*tc, motive, lhs_fn, rhs_fn, *fn_pr, pr);
        }

        assign(subst, g, pr);
        proof_state new_ps(s, to_list(new_goals.begin(), new_goals.end(), tail(gs)), subst, ngen);
        if (solve_constraints(env, ios, new_ps, cs))
            return some_proof_state(new_ps);
        return none_proof_state();
    };
    return tactic01(fn);
}
void initialize_congruence_tactic() { register_simple_tac(name{"tactic", "congruence"}, congruence_tactic); }
void finalize_congruence_tactic() {}
}
