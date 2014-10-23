/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/unifier.h"
#include "library/reducible.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic exact_tactic(elaborate_fn const & elab, expr const & e) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & s) {
            name_generator ngen = s.get_ngen();
            substitution subst  = s.get_subst();
            goals const & gs    = s.get_goals();
            if (empty(gs))
                return none_proof_state();
            goal const & g      = head(gs);
            expr       new_e;
            buffer<constraint> cs;
            auto ecs = elab(g, ngen.mk_child(), e);
            new_e    = ecs.first;
            to_buffer(ecs.second, cs);
            to_buffer(s.get_postponed(), cs);
            unifier_config cfg(ios.get_options());
            unify_result_seq rseq = unify(env, cs.size(), cs.data(), ngen.mk_child(), subst, cfg);
            if (auto p = rseq.pull()) {
                substitution new_subst     = p->first.first;
                constraints  new_postponed = p->first.second;
                new_e = new_subst.instantiate(new_e);
                bool relax_main_opaque = true;
                auto tc     = mk_type_checker(env, ngen.mk_child(), relax_main_opaque);
                auto e_t_cs = tc->infer(new_e);
                expr t      = new_subst.instantiate(g.get_type());
                auto dcs    = tc->is_def_eq(e_t_cs.first, t);
                if (dcs.first && !dcs.second && !e_t_cs.second) {
                    expr new_p = g.abstract(new_e);
                    check_has_no_local(new_p, e, "exact");
                    new_subst.assign(g.get_name(), new_p);
                    return some(proof_state(tail(gs), new_subst, ngen, new_postponed));
                }
            }
            return none_proof_state();
        });
}

static expr * g_exact_tac_fn      = nullptr;

expr const & get_exact_tac_fn() { return *g_exact_tac_fn; }

void initialize_exact_tactic() {
    name exact_tac_name({"tactic", "exact"});
    g_exact_tac_fn      = new expr(Const(exact_tac_name));
    register_tac(exact_tac_name,
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'exact' tactic, invalid argument");
                     return exact_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });
}
void finalize_exact_tactic() {
    delete g_exact_tac_fn;
}
}
