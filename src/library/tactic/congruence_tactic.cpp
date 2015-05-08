/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/tactic/util.h"
#include "library/tactic/intros_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
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

        buffer<goal> new_goals;

        auto mk_eq_goal = [&](expr const & lhs, expr const & rhs) {
            expr new_type = mk_eq(*tc, lhs, rhs);
            expr new_meta = g.mk_meta(ngen.next(), new_type);
            new_goals.push_back(goal(new_meta, new_type));
            return some_expr(new_meta);
        };

        std::function<optional<expr>(expr const &, expr const &, bool)> process =
        [&](expr const & lhs, expr const & rhs, bool first) {
            if (tc->is_def_eq(lhs, rhs, justification(), cs)) {
                return some_expr(mk_refl(*tc, lhs));
            }
            if (!is_app(lhs) || !is_app(rhs)) {
                if (first) {
                    throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, left (and right) hand side of equation must be a function application");
                    return none_expr();
                }
                return mk_eq_goal(lhs, rhs);
            }
            expr lhs_fn = app_fn(lhs);
            expr rhs_fn = app_fn(rhs);
            expr lhs_fn_type = tc->whnf(tc->infer(lhs_fn, cs), cs);
            expr rhs_fn_type = tc->whnf(tc->infer(rhs_fn, cs), cs);
            if (!tc->is_def_eq(lhs_fn_type, rhs_fn_type, justification(), cs)) {
                if (first) {
                    throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, functions do not have the same type");
                    return none_expr();
                }
                return mk_eq_goal(lhs, rhs);
            }
            expr fn_type;
            if (is_pi(lhs_fn_type)) {
                fn_type = lhs_fn_type;
            } else if (is_pi(rhs_fn_type)) {
                fn_type = rhs_fn_type;
            } else if (first) {
                throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, failed to compute function type");
                return none_expr();
            } else {
                return mk_eq_goal(lhs, rhs);
            }

            if (!closed(binding_body(fn_type))) {
                if (first) {
                    throw_tactic_exception_if_enabled(s, "invalid 'congruence' tactic, cannot be applied to dependent functions");
                    return none_expr();
                }
                return mk_eq_goal(lhs, rhs);
            }

            expr lhs_arg = app_arg(lhs);
            expr rhs_arg = app_arg(rhs);
            expr arg_pr;
            if (tc->is_def_eq(lhs_arg, rhs_arg, justification(), cs)) {
                arg_pr = mk_refl(*tc, lhs_arg);
            } else {
                arg_pr = *mk_eq_goal(lhs_arg, rhs_arg);
            }

            optional<expr> opt_fn_pr = process(lhs_fn, rhs_fn, false);
            if (!opt_fn_pr)
                return none_expr();
            expr fn_pr = *opt_fn_pr;

            expr A   = binding_domain(fn_type);
            expr B   = binding_body(fn_type);
            level l1 = sort_level(tc->ensure_type(A, cs));
            level l2 = sort_level(tc->ensure_type(B, cs));

            return some_expr(mk_app({mk_constant(get_congr_name(), {l1, l2}),
                            A, B, lhs_fn, rhs_fn, lhs_arg, rhs_arg, fn_pr, arg_pr}));
        };

        if (optional<expr> pr = process(lhs, rhs, true)) {
            std::reverse(new_goals.begin(), new_goals.end());
            assign(subst, g, *pr);
            proof_state new_ps(s, to_list(new_goals.begin(), new_goals.end(), tail(gs)), subst, ngen);
            if (solve_constraints(env, ios, new_ps, cs))
                return some_proof_state(new_ps);
        }
        return none_proof_state();
    };
    return tactic01(fn);
}
void initialize_congruence_tactic() { register_simple_tac(name{"tactic", "congruence"}, congruence_tactic); }
void finalize_congruence_tactic() {}
}
