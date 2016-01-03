/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/expr_to_tactic.h"
#include "library/blast/blast.h"
#include "library/blast/blast_exception.h"

namespace lean {
tactic mk_blast_tactic(list<name> const & ls, list<name> const & ds) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & _s) {
            proof_state s = apply_substitution(_s);
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            goal const & g = head(gs);
            try {
                pair<expr, constraint_seq> pr_cs = blast_goal(env, ios, ls, ds, g);
                expr pr                = pr_cs.first;
                constraint_seq cs      = pr_cs.second;
                goals new_gs           = tail(gs);
                substitution new_subst = s.get_subst();
                assign(new_subst, g, pr);
                proof_state new_ps(s, new_gs, new_subst);
                if (solve_constraints(env, ios, new_ps, cs))
                    return some_proof_state(new_ps);
                return none_proof_state();
            } catch (blast_exception & ex) {
                throw_tactic_exception_if_enabled(s, ex.what());
                return none_proof_state();
            }
        });
}

void initialize_blast_tactic() {
    register_tac(name{"tactic", "blast"},
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 2)
                         throw expr_to_tactic_exception(e, "invalid 'blast' tactic, incorrect number of arguments");
                     buffer<name> ls, ds;
                     get_tactic_id_list_elements(args[0], ls, "invalid 'blast' tactic, list of identifiers expected");
                     get_tactic_id_list_elements(args[1], ds, "invalid 'blast' tactic, list of identifiers expected");
                     return mk_blast_tactic(to_list(ls), to_list(ds));
                 });
}
void finalize_blast_tactic() {
}
}
