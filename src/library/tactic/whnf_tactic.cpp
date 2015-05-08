/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/reducible.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/whnf_tactic.h"

namespace lean {
tactic whnf_tactic() {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & ps) {
            goals const & gs = ps.get_goals();
            if (empty(gs))
                return none_proof_state();
            name_generator ngen = ps.get_ngen();
            auto tc             = mk_type_checker(env, ngen.mk_child());
            goal  g             = head(gs);
            goals tail_gs       = tail(gs);
            expr  type          = g.get_type();
            auto t_cs           = tc->whnf(type);
            goals new_gs(goal(g.get_meta(), t_cs.first), tail_gs);
            proof_state new_ps(ps, new_gs, ngen);
            if (solve_constraints(env, ios, new_ps, t_cs.second)) {
                return some_proof_state(new_ps);
            } else {
                return none_proof_state();
            }
        });
}

void initialize_whnf_tactic() {
    register_tac(get_tactic_whnf_name(),
                 [](type_checker &, elaborate_fn const &, expr const &, pos_info_provider const *) {
                     return whnf_tactic();
                 });
}

void finalize_whnf_tactic() {
}
}
