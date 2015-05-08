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
tactic exfalso_tactic() {
    auto fn = [=](environment const & env, io_state const &, proof_state const & s) {
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
        expr false_expr     = mk_false(env);
        expr new_meta       = g.mk_meta(ngen.next(), false_expr);
        goal new_goal(new_meta, false_expr);
        assign(subst, g, mk_false_rec(*tc, new_meta, t));
        return some(proof_state(s, goals(new_goal, tail(gs)), subst, ngen));
    };
    return tactic01(fn);
}
void initialize_exfalso_tactic() {
    register_tac(name{"tactic", "exfalso"},
                 [](type_checker &, elaborate_fn const &, expr const &, pos_info_provider const *) {
                     return exfalso_tactic();
                 });
}
void finalize_exfalso_tactic() {
}
}
