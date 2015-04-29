/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lazy_list_fn.h"
#include "kernel/type_checker.h"
#include "kernel/error_msgs.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/tactic/tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic change_goal_tactic(elaborate_fn const & elab, expr const & e) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            proof_state new_s = s;
            goals const & gs  = new_s.get_goals();
            if (!gs) {
                throw_no_goal_if_enabled(s);
                return proof_state_seq();
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
                if (tc->is_def_eq(t, *new_e, justification(), cs)) {
                    if (cs) {
                        unifier_config cfg(ios.get_options());
                        buffer<constraint> cs_buf;
                        cs.linearize(cs_buf);
                        to_buffer(new_s.get_postponed(), cs_buf);
                        unify_result_seq rseq = unify(env, cs_buf.size(), cs_buf.data(), ngen.mk_child(), subst, cfg);
                        return map2<proof_state>(rseq, [=](pair<substitution, constraints> const & p) -> proof_state {
                                substitution const & subst    = p.first;
                                constraints const & postponed = p.second;
                                name_generator new_ngen(ngen);
                                substitution new_subst = subst;
                                expr final_e = new_subst.instantiate_all(*new_e);
                                expr M       = g.mk_meta(new_ngen.next(), final_e);
                                goal new_g(M, final_e);
                                assign(new_subst, g, M);
                                return proof_state(new_s, cons(new_g, tail(gs)), new_subst, new_ngen, postponed);
                            });
                    }
                    expr M   = g.mk_meta(ngen.next(), *new_e);
                    goal new_g(M, *new_e);
                    assign(subst, g, M);
                    return proof_state_seq(proof_state(new_s, cons(new_g, tail(gs)), subst, ngen));
                } else {
                    throw_tactic_exception_if_enabled(new_s, [=](formatter const & fmt) {
                            format r = format("invalid 'change' tactic, the given type");
                            r += pp_indent_expr(fmt, *new_e);
                            r += compose(line(), format("does not match the goal type"));
                            r += pp_indent_expr(fmt, t);
                            return r;
                        });
                    return proof_state_seq();
                }
            }
            return proof_state_seq();
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
