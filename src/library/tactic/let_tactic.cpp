/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
expr mk_let_tactic_expr(name const & id, expr const & e) {
    return mk_app(mk_constant(get_tactic_lettac_name()),
                  mk_constant(id), e);
}

tactic let_tactic(elaborate_fn const & elab, name const & id, expr const & e) {
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) {
            proof_state new_s = s;
            goals const & gs  = new_s.get_goals();
            if (!gs) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            goal const & g         = head(gs);
            name_generator ngen    = s.get_ngen();
            bool report_unassigned = true;
            elaborate_result esc = elab(g, ngen.mk_child(), e, none_expr(), new_s.get_subst(), report_unassigned);
            expr new_e; substitution new_subst; constraints cs;
            std::tie(new_e, new_subst, cs) = esc;
            if (cs)
                throw_tactic_exception_if_enabled(s, "invalid 'let' tactic, fail to resolve generated constraints");
            auto tc         = mk_type_checker(env, ngen.mk_child());
            expr new_e_type = tc->infer(new_e).first;
            expr new_local  = mk_local(ngen.next(), id, new_e_type, binder_info());
            buffer<expr> hyps;
            g.get_hyps(hyps);
            hyps.push_back(new_local);
            expr new_mvar  = mk_metavar(ngen.next(), Pi(hyps, g.get_type()));
            hyps.pop_back();
            expr new_meta_core = mk_app(new_mvar, hyps);
            expr new_meta      = mk_app(new_meta_core, new_local);
            goal new_goal(new_meta, g.get_type());
            assign(new_subst, g, mk_app(new_meta_core, new_e));
            return some_proof_state(proof_state(s, cons(new_goal, tail(gs)), new_subst, ngen));
        });
}

void initialize_let_tactic() {
    register_tac(get_tactic_lettac_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     name id = tactic_expr_to_id(app_arg(app_fn(e)), "invalid 'let' tactic, argument must be an identifier");
                     check_tactic_expr(app_arg(e), "invalid 'let' tactic, argument must be an expression");
                     return let_tactic(fn, id, get_tactic_expr_expr(app_arg(e)));
                 });
}
void finalize_let_tactic() {
}
}
