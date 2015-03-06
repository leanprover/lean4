/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "kernel/type_checker.h"
#include "library/reducible.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic change_goal_tactic(elaborate_fn const & elab, expr const & e) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & s) {
            proof_state new_s = s;
            goals const & gs  = new_s.get_goals();
            if (!gs) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            expr t            = head(gs).get_type();
            bool report_unassigned = true;
            if (auto new_e = elaborate_with_respect_to(env, ios, elab, new_s, e, none_expr(), report_unassigned)) {
                goals const & gs    = new_s.get_goals();
                goal const & g      = head(gs);
                name_generator ngen = new_s.get_ngen();
                substitution subst  = new_s.get_subst();
                auto tc             = mk_type_checker(env, ngen.mk_child());
                constraint_seq cs;
                if (tc->is_def_eq(t, *new_e, justification(), cs) && !cs) {
                    expr M   = g.mk_meta(ngen.next(), *new_e);
                    goal new_g(M, *new_e);
                    expr val = g.abstract(M);
                    subst.assign(g.get_name(), val);
                    return some(proof_state(new_s, cons(new_g, tail(gs)), subst, ngen));
                } else {
                    // generate error
                    return none_proof_state();
                }
            }
            return none_proof_state();
        });
}

void initialize_change_tactic() {
    register_tac(get_tactic_change_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'change' tactic, invalid argument");
                     return change_goal_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });
}
void finalize_change_tactic() {
}
}
