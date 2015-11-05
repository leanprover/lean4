/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/normalize.h"
#include "library/norm_num.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic norm_num_tactic() {
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            goal const & g = head(gs);
            expr const & c = g.get_type();
            expr lhs, rhs;
            if (!is_eq(c, lhs, rhs)) {
                throw_tactic_exception_if_enabled(s, "norm_num tactic failed, conclusion is not an equality");
                return none_proof_state();
            }
            type_checker_ptr rtc = mk_type_checker(env, UnfoldReducible);
            lhs = normalize(*rtc, lhs);
            rhs = normalize(*rtc, rhs);
            buffer<expr> hyps;
            g.get_hyps(hyps);
            local_context ctx(to_list(hyps));
            //std::cout << "\nnum of lhs: " << mpq_of_expr(env, ctx, lhs) << "\n";
            try {
                pair<expr, expr> p = mk_norm_num(env, ctx, lhs);
                //std::cout << "checkpt 0";
                expr new_lhs = p.first;
                expr new_lhs_pr  = p.second;
                pair<expr, expr> p2 = mk_norm_num(env, ctx, rhs);
                expr new_rhs = p2.first;
                expr new_rhs_pr = p2.second;
                mpq v_lhs = mpq_of_expr(env, ctx, new_lhs), v_rhs = mpq_of_expr(env, ctx, new_rhs);
                if (v_lhs == v_rhs) {
                    // std::cout << "checkpt 1\n";
                    type_checker tc(env);
                    //std::cout << "checkpt 2: " << new_lhs_pr << ", \n" << new_rhs_pr << "\n";
                    expr g_prf = mk_trans(tc, new_lhs_pr, mk_symm(tc, new_rhs_pr));
                    //std::cout << "checkpt 3\n";
                    substitution new_subst = s.get_subst();
                    assign(new_subst, g, g_prf);
                    return some_proof_state(proof_state(s, tail(gs), new_subst));
                } else {
                    std::cout << "lhs: " << new_lhs << ", rhs: " << new_rhs << "\n";
                    throw_tactic_exception_if_enabled(s, "norm_num tactic failed, lhs doesn't match rhs");
                    return none_proof_state();
                }

            } catch (exception & ex) {
                throw_tactic_exception_if_enabled(s, ex.what());
                return none_proof_state();
            }
        });
}

void initialize_norm_num_tactic() {
    register_tac(name{"tactic", "norm_num"},
                 [](type_checker &, elaborate_fn const &, expr const &, pos_info_provider const *) {
                     return norm_num_tactic();
                 });
}
void finalize_norm_num_tactic() {
}
}
