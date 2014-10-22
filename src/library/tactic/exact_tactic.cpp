/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic exact_tactic(expr const & _e) {
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) {
            type_checker tc(env);
            substitution subst  = s.get_subst();
            goals const & gs    = s.get_goals();
            goal const & g      = head(gs);
            expr e              = subst.instantiate(_e);
            auto e_t_cs         = tc.infer(e);
            expr e_t            = subst.instantiate(e_t_cs.first);
            expr t              = subst.instantiate(g.get_type());
            auto dcs            = tc.is_def_eq(e_t, t);
            if (dcs.first && !dcs.second && !e_t_cs.second) {
                expr new_p = g.abstract(e);
                check_has_no_local(new_p, _e, "exact");
                subst.assign(g.get_name(), new_p);
                return some(proof_state(s, tail(gs), subst));
            } else {
                return none_proof_state();
            }
        });
}

static expr * g_exact_tac_fn      = nullptr;

expr const & get_exact_tac_fn() { return *g_exact_tac_fn; }

void initialize_exact_tactic() {
    name exact_tac_name({"tactic", "exact"});
    g_exact_tac_fn      = new expr(Const(exact_tac_name));
    register_tac(exact_tac_name,
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     // TODO(Leo): use elaborate_fn
                     return exact_tactic(app_arg(e));
                 });
}
void finalize_exact_tactic() {
    delete g_exact_tac_fn;
}
}
