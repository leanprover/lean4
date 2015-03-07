/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "kernel/type_checker.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic exact_tactic(elaborate_fn const & elab, expr const & e, bool enforce_type_during_elaboration) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & s) {
            proof_state new_s = s;
            goals const & gs  = new_s.get_goals();
            if (!gs) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            expr t            = head(gs).get_type();
            bool report_unassigned = false;
            if (auto new_e = elaborate_with_respect_to(env, ios, elab, new_s, e, some_expr(t),
                                                       report_unassigned, enforce_type_during_elaboration)) {
                goals const & gs   = new_s.get_goals();
                goal const & g     = head(gs);
                expr new_p         = g.abstract(*new_e);
                substitution subst = new_s.get_subst();
                check_has_no_local(new_p, e, "exact");
                subst.assign(g.get_name(), new_p);
                return some(proof_state(new_s, tail(gs), subst));
            }
            return none_proof_state();
        });
}

static expr * g_exact_tac_fn      = nullptr;
static expr * g_sexact_tac_fn      = nullptr;
expr const & get_exact_tac_fn()  { return *g_exact_tac_fn; }
expr const & get_sexact_tac_fn() { return *g_sexact_tac_fn; }
void initialize_exact_tactic() {
    name const & exact_tac_name = get_tactic_exact_name();
    name const & sexact_tac_name = get_tactic_sexact_name();
    g_exact_tac_fn      = new expr(Const(exact_tac_name));
    g_sexact_tac_fn     = new expr(Const(sexact_tac_name));
    register_tac(exact_tac_name,
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'exact' tactic, invalid argument");
                     return exact_tactic(fn, get_tactic_expr_expr(app_arg(e)), false);
                 });
    register_tac(sexact_tac_name,
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'exact' tactic, invalid argument");
                     return exact_tactic(fn, get_tactic_expr_expr(app_arg(e)), true);
                 });
}
void finalize_exact_tactic() {
    delete g_exact_tac_fn;
}
}
