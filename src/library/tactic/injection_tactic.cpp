/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/clear_tactic.h"

namespace lean {
tactic injection_tactic_core(expr const & e, unsigned num, list<name> const & ids, bool report_errors);

// Return true iff lhs and rhs are of the form (f ...) f is a constructor
bool is_injection_target(type_checker & tc, expr lhs, expr rhs) {
    environment const & env = tc.env();
    lhs = tc.whnf(lhs).first;
    rhs = tc.whnf(rhs).first;
    expr A = tc.whnf(tc.infer(lhs).first).first;
    expr const & I = get_app_fn(A);
    if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I)))
        return false;
    expr lhs_fn = get_app_fn(lhs);
    expr rhs_fn = get_app_fn(rhs);
    return
        is_constant(lhs_fn) && is_constant(rhs_fn) &&
        const_name(lhs_fn) == const_name(rhs_fn) &&
        inductive::is_intro_rule(env, const_name(lhs_fn));
}

/** \brief Introduce num hypotheses, if _ns is not nil use it to name the hypothesis,

    New hypothesis of the form (a = a) and (a == a) are discarded.
    New hypothesis of the form (a == b) where (a b : A), are converted into (a = b).
*/
tactic intros_num_tactic(unsigned num, list<name> _ns) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        if (num == 0)
            return proof_state_seq(s);
        list<name> ns    = _ns;
        goals const & gs = s.get_goals();
        if (empty(gs))
            return proof_state_seq();
        goal const & g      = head(gs);
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child());
        expr t              = g.get_type();
        expr m              = g.get_meta();

        auto mk_name = [&](name const & n) {
            if (is_nil(ns)) {
                return g.get_unused_name(n);
            } else {
                name r = head(ns);
                ns     = tail(ns);
                return r;
            }
        };

        auto keep_hyp = [&]() {
            expr H = mk_local(mk_name(binding_name(t)), binding_domain(t));
            t      = instantiate(binding_body(t), H);
            m      = mk_app(m, H);
            proof_state new_s(s, cons(goal(m, t), tail(gs)), ngen);
            return intros_num_tactic(num-1, ns)(env, ios, new_s);
        };

        auto discard_hyp = [&]() {
            expr new_meta = g.mk_meta(ngen.next(), binding_body(t));
            goal new_goal(new_meta, binding_body(t));
            substitution new_subst = s.get_subst();
            assign(new_subst, g, mk_lambda(binding_name(t), binding_domain(t), new_meta));
            proof_state new_s(s, cons(new_goal, tail(gs)), new_subst, ngen);
            return intros_num_tactic(num-1, ns)(env, ios, new_s);
        };

        t = tc->ensure_pi(t).first;

        // if goal depends on hypothesis, we keep it
        if (!closed(binding_body(t)))
            return keep_hyp();

        constraint_seq cs;
        expr Htype = tc->whnf(binding_domain(t), cs);

        // new unification constraints were generated, so we keep hypothesis
        if (cs)
            return keep_hyp();

        expr lhs, rhs;
        if (is_eq(Htype, lhs, rhs)) {
            // equalities of the form (a = a) are discarded
            if (tc->is_def_eq(lhs, rhs, justification(), cs) && !cs) {
                return discard_hyp();
            } else if (is_injection_target(*tc, lhs, rhs)) {
                // apply injection recursively
                name Hname = ngen.next();
                expr H     = mk_local(Hname, binding_domain(t));
                t          = binding_body(t);
                m          = mk_app(m, H);
                proof_state new_s(s, cons(goal(m, t), tail(gs)), ngen);
                return then(injection_tactic_core(H, num-1, ns, false),
                            clear_tactic(Hname))(env, ios, new_s);
            } else {
                return keep_hyp();
            }
        }

        expr A, B;
        if (is_standard(env) && is_heq(Htype, A, lhs, B, rhs)) {
            if (tc->is_def_eq(A, B, justification(), cs) && !cs) {
                // since types A and B are definitionally equal, we convert to homogeneous
                expr new_eq    = mk_eq(*tc, lhs, rhs);
                expr new_type  = mk_pi(binding_name(t), new_eq, binding_body(t));
                expr new_meta  = g.mk_meta(ngen.next(), new_type);
                goal new_goal(new_meta, new_type);
                expr H         = mk_local(ngen.next(), binding_domain(t));
                levels heq_lvl = const_levels(get_app_fn(Htype));
                expr arg       = mk_app(mk_constant(get_heq_to_eq_name(), heq_lvl), A, lhs, rhs, H);
                expr V         = Fun(H, mk_app(new_meta, arg));
                substitution new_subst = s.get_subst();
                assign(new_subst, g, V);
                proof_state new_s(s, cons(new_goal, tail(gs)), new_subst, ngen);
                return intros_num_tactic(num, ns)(env, ios, new_s);
            } else {
                return keep_hyp();
            }
        }

        // hypothesis is not an equality
        return keep_hyp();
    };
    return tactic(fn);
}

tactic injection_tactic_core(expr const & e, unsigned num, list<name> const & ids, bool report_errors) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        goals const & gs  = s.get_goals();
        if (!gs) {
            throw_no_goal_if_enabled(s);
            return proof_state_seq();
        }
        expr t                 = head(gs).get_type();
        constraint_seq cs;
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child());
        expr e_type         = tc->whnf(tc->infer(e, cs), cs);
        expr lhs, rhs;
        if (!is_eq(e_type, lhs, rhs)) {
            if (report_errors) {
                throw_tactic_exception_if_enabled(s, "invalid 'injection' tactic, "
                                                  "given argument is not an equality proof");
                return proof_state_seq();
            }
            return intros_num_tactic(num, ids)(env, ios, s);
        }
        lhs = tc->whnf(lhs, cs);
        rhs = tc->whnf(rhs, cs);
        expr A = tc->whnf(tc->infer(lhs, cs), cs);
        buffer<expr> I_args;
        expr I = get_app_args(A, I_args);
        if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I))) {
            if (report_errors) {
                throw_tactic_exception_if_enabled(s, "invalid 'injection' tactic, "
                                                  "it is not an equality between inductive values");
                return proof_state_seq();
            }
            return intros_num_tactic(num, ids)(env, ios, s);
        }
        expr lhs_fn = get_app_fn(lhs);
        expr rhs_fn = get_app_fn(rhs);
        if (!is_constant(lhs_fn) || !is_constant(rhs_fn) || const_name(lhs_fn) != const_name(rhs_fn) ||
            !inductive::is_intro_rule(env, const_name(lhs_fn))) {
            if (report_errors) {
                throw_tactic_exception_if_enabled(s, "invalid 'injection' tactic, "
                                                  "the given equality is not of the form (f ...) = (f ...) "
                                                  "where f is a constructor");
                return proof_state_seq();
            }
            return intros_num_tactic(num, ids)(env, ios, s);
        }
        unsigned num_params  = *inductive::get_num_params(env, const_name(I));
        unsigned cnstr_arity = get_arity(env.get(const_name(lhs_fn)).get_type());
        lean_assert(cnstr_arity >= num_params);
        unsigned num_new_eqs = cnstr_arity - num_params;
        level t_lvl = sort_level(tc->ensure_type(t, cs));
        expr N      = mk_constant(name(const_name(I), "no_confusion"), cons(t_lvl, const_levels(I)));
        N           = mk_app(mk_app(N, I_args), t, lhs, rhs, e);
        proof_state new_s(s, ngen);
        if (is_standard(env)) {
            tactic tac = then(take(apply_tactic_core(N, cs), 1),
                              intros_num_tactic(num + num_new_eqs, ids));
            return tac(env, ios, new_s);
        } else {
            level n_lvl    = mk_meta_univ(tc->mk_fresh_name());
            expr lift_down = mk_app(mk_constant(get_lift_down_name(), {t_lvl, n_lvl}), t);
            tactic tac     = then(take(apply_tactic_core(lift_down), 1),
                                  then(take(apply_tactic_core(N, cs), 1),
                                       intros_num_tactic(num + num_new_eqs, ids)));
            return tac(env, ios, new_s);
        }
    };
    return tactic(fn);
};

tactic injection_tactic(elaborate_fn const & elab, expr const & e, list<name> const & ids) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        proof_state new_s = s;
        goals const & gs  = new_s.get_goals();
        if (!gs) {
            throw_no_goal_if_enabled(s);
            return proof_state_seq();
        }
        expr t                 = head(gs).get_type();
        bool report_unassigned = true;
        bool enforce_type      = false;
        if (optional<expr> new_e = elaborate_with_respect_to(env, ios, elab, new_s, e, none_expr(),
                                                             report_unassigned, enforce_type)) {
            return injection_tactic_core(*new_e, 0, ids, true)(env, ios, new_s);
        } else {
            return proof_state_seq();
        }
    };
    return tactic(fn);
}

void initialize_injection_tactic() {
    register_tac(name{"tactic", "injection"},
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(app_fn(e)), "invalid 'injection' tactic, invalid argument");
                     buffer<name> ids;
                     get_tactic_id_list_elements(app_arg(e), ids, "invalid 'injection' tactic, list of identifiers expected");
                     return take(injection_tactic(fn, get_tactic_expr_expr(app_arg(app_fn(e))), to_list(ids)), 1);
                 });
}

void finalize_injection_tactic() {
}
}
