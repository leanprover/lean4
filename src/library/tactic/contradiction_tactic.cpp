/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/tactic/intros_tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "kernel/kernel_exception.h"

namespace lean {
tactic contradiction_tactic() {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return optional<proof_state>();
        }
        goal const & g      = head(gs);
        expr const & t      = g.get_type();
        substitution subst  = s.get_subst();
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child());
        auto conserv_tc     = mk_type_checker(env, ngen.mk_child(), UnfoldReducible);
        buffer<expr> hyps;
        g.get_hyps(hyps);
        for (expr const & h : hyps) {
            expr h_type = mlocal_type(h);
            h_type      = tc->whnf(h_type).first;
            expr lhs, rhs, arg;
            if (is_false(env, h_type)) {
                assign(subst, g, mk_false_rec(*tc, h, t));
                return some_proof_state(proof_state(s, tail(gs), subst, ngen));
            } else if (is_not(env, h_type, arg)) {
                optional<expr> h_pos;
                for (expr const & h_prime : hyps) {
                    constraint_seq cs;
                    if (conserv_tc->is_def_eq(arg, mlocal_type(h_prime), justification(), cs) && !cs) {
                        h_pos = h_prime;
                        break;
                    }
                }
                if (h_pos) {
                    assign(subst, g, mk_absurd(*tc, t, *h_pos, h));
                    return some_proof_state(proof_state(s, tail(gs), subst, ngen));
                }
            } else if (is_eq(h_type, lhs, rhs)) {
                lhs = tc->whnf(lhs).first;
                rhs = tc->whnf(rhs).first;
                optional<name> lhs_c = is_constructor_app(env, lhs);
                optional<name> rhs_c = is_constructor_app(env, rhs);
                if (lhs_c && rhs_c && *lhs_c != *rhs_c) {
                    if (optional<name> I_name = inductive::is_intro_rule(env, *lhs_c)) {
                        name no_confusion(*I_name, "no_confusion");
                        try {
                            expr I      = tc->whnf(tc->infer(lhs).first).first;
                            buffer<expr> args;
                            expr I_fn   = get_app_args(I, args);
                            if (is_constant(I_fn)) {
                                level t_lvl = sort_level(tc->ensure_type(t).first);
                                expr V = mk_app(mk_app(mk_constant(no_confusion, cons(t_lvl, const_levels(I_fn))), args),
                                                t, lhs, rhs, h);
                                if (auto r = lift_down_if_hott(*tc, V)) {
                                    check_term(*tc, *r);
                                    assign(subst, g, *r);
                                    return some_proof_state(proof_state(s, tail(gs), subst, ngen));
                                }
                            }
                        } catch (kernel_exception & ex) {
                            regular(env, ios) << ex << "\n";
                        }
                    }
                }
            }
        }
        return none_proof_state();
    };
    return tactic01(fn);
}

void initialize_contradiction_tactic() {
    register_tac(name{"tactic", "contradiction"},
                 [](type_checker &, elaborate_fn const &, expr const &, pos_info_provider const *) {
                     list<name> empty;
                     return then(orelse(intros_tactic(empty), id_tactic()), contradiction_tactic());
                 });
}
void finalize_contradiction_tactic() {
}
}
