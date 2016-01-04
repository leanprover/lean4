 /*
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/

#include "library/tactic/replace_tactic.h"
#include "util/lazy_list_fn.h"
#include "kernel/error_msgs.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/tactic/expr_to_tactic.h"
#include "kernel/instantiate.h"

namespace lean {


static expr * g_replace_tac = nullptr;

expr substitute_at_occurrences(environment const & env, expr const & t, expr const & nexpr, expr const & oexpr, occurrence const & occ) {
    bool has_dep_elim = inductive::has_dep_elim(env, get_eq_name());
    unsigned vidx = has_dep_elim ? 1 : 0;
    optional<expr> nt = replace_occurrences(t, oexpr, occ, vidx);
    if (!nt) {
        return t;
    }
    expr t2 = instantiate(*nt, vidx, nexpr);
    return t2;
}

tactic mk_replace_tactic(elaborate_fn const & elab, expr const & e) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            buffer<expr> e_args;
            get_app_args(e, e_args);
            expr t1, t2; // replace t2 with t1
            location loc;
            if (e_args.size() == 3) {
                t1 = get_tactic_expr_expr(e_args[1]);
                t2 = get_tactic_expr_expr(e_args[0]);
                if (is_location_expr(get_tactic_expr_expr(e_args[2]))) {
                    loc = get_location_expr_location(get_tactic_expr_expr(e_args[2]));
                } else {
                    loc = location();
                }
            } else {
                throw_tactic_exception_if_enabled(s, "malformed arguments to replace");
                return proof_state_seq();
            }
            proof_state new_s = s;
            goals const & gs  = new_s.get_goals();
            if (!gs) {
                throw_no_goal_if_enabled(s);
                return proof_state_seq();
            }
            expr t            = head(gs).get_type();
            bool report_unassigned = true;
            auto new_t1 =  elaborate_with_respect_to(env, ios, elab, new_s, t1, none_expr(), report_unassigned);
            auto new_t2 =  elaborate_with_respect_to(env, ios, elab, new_s, t2, none_expr(), report_unassigned);
            if (new_t1 && new_t2) {
                goals const & gs    = new_s.get_goals();
                goal const & g      = head(gs);
                name_generator ngen = new_s.get_ngen();
                substitution subst  = new_s.get_subst();
                auto tc             = mk_type_checker(env, ngen.mk_child());
                constraint_seq cs;
                if (tc->is_def_eq(*new_t1, *new_t2, justification(), cs)) {
                    auto nocc = loc.includes_goal();
                    expr new_goal;
                    if (nocc) {
                        new_goal = substitute_at_occurrences(env, g.get_type(), *new_t1, *new_t2, *nocc);
                    } else {
                        throw_tactic_exception_if_enabled(s, "replacing in hypotheses not implemented");
                        return proof_state_seq();
                    }
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
                                expr M = g.mk_meta(new_ngen.next(), new_goal);
                                goal new_g(M, new_goal);
                                assign(new_subst, g, M);
                                return proof_state(new_s, cons(new_g, tail(gs)), new_subst, new_ngen, postponed);
                            });
                    }
                    expr M   = g.mk_meta(ngen.next(), new_goal);
                    goal new_g(M, new_goal);
                    assign(subst, g, M);
                    return proof_state_seq(proof_state(new_s, cons(new_g, tail(gs)), subst, ngen));
                } else {
                    throw_tactic_exception_if_enabled(new_s, [=](formatter const & fmt) {
                            format r = format("invalid 'replace' tactic, the new type");
                            r += pp_indent_expr(fmt, *new_t1);
                            r += compose(line(), format("does not match the old type"));
                            r += pp_indent_expr(fmt, *new_t2);
                            return r;
                        });
                    return proof_state_seq();
                }
            }
            return proof_state_seq();
        });
}

void initialize_replace_tactic() {
    name replace_tac_name{"tactic", "replace"};
    g_replace_tac          = new expr(Const(replace_tac_name));
    register_tac(replace_tac_name,
                 [](type_checker &, elaborate_fn const & elab, expr const & e, pos_info_provider const *) {
                     return mk_replace_tactic(elab, e);
                 });
}

void finalize_replace_tactic() {
    delete g_replace_tac;
}

}
