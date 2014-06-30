/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/lazy_list_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/kernel_bindings.h"
#include "library/unifier.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
/**
   \brief Traverse \c e and collect metavariable applications (?m l1 ... ln), and store in result.
   The function only succeeds if all metavariable applications are "simple", i.e., the arguments
   are distinct local constants.
*/
bool collect_simple_metas(expr const & e, buffer<expr> & result) {
    bool failed = false;
    // collect metavariables
    for_each(e, [&](expr const & e, unsigned) {
            if (is_meta(e)) {
                if (!is_simple_meta(e)) {
                    failed = true;
                } else {
                    result.push_back(e);
                    return false; /* do not visit type */
                }
            }
            return !failed && has_metavar(e);
        });
    return !failed;
}

tactic apply_tactic(expr const & e) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            if (s.is_final_state()) {
                return proof_state_seq();
            }
            goals const & gs    = s.get_goals();
            name gname          = head(gs).first;
            goal  g             = head(gs).second;
            goals rest_gs       = tail(gs);
            expr const & C      = g.get_conclusion();
            name_generator ngen = s.ngen();
            type_checker tc(env, ngen.mk_child());
            expr new_e          = e;
            expr new_e_type     = tc.infer(new_e);
            buffer<expr> meta_buffer;
            if (!collect_simple_metas(new_e, meta_buffer))
                return proof_state_seq();
            // add more metavariables while new_e_type is a Pi
            while (is_pi(new_e_type)) {
                expr meta  = g.mk_meta(ngen.next(), binding_domain(new_e_type));
                meta_buffer.push_back(meta);
                new_e      = mk_app(new_e, meta);
                new_e_type = instantiate(binding_body(new_e_type), meta);
            }
            list<expr> metas = to_list(meta_buffer.begin(), meta_buffer.end());
            // TODO(Leo): we should use unifier plugin
            lazy_list<substitution> substs = unify(env, C, new_e_type, ngen.mk_child(), ios.get_options());
            return map2<proof_state>(substs, [=](substitution const & subst) -> proof_state {
                    // apply substitution to remaining goals
                    name_generator new_ngen(ngen);
                    type_checker tc(env, new_ngen.mk_child());
                    goals new_gs = map(rest_gs, [&](named_goal const & ng) {
                            return named_goal(ng.first, ng.second.instantiate_metavars(subst));
                        });
                    expr P            = subst.instantiate_metavars_wo_jst(new_e);
                    goal tmp_g        = g.instantiate_metavars(subst);
                    unsigned subgoal_idx = 1;
                    buffer<std::pair<name, expr>> trace_buffer;
                    // add unassigned metavariables as new goals
                    buffer<named_goal> subgoals;
                    for (expr const & meta : metas) {
                        if (!subst.is_assigned(get_app_fn(meta))) {
                            name new_gname(gname, subgoal_idx);
                            expr new_C = subst.instantiate_metavars_wo_jst(tc.infer(meta));
                            goal new_g(tmp_g.get_hypotheses(), new_C);
                            subgoals.emplace_back(new_gname, new_g);
                            trace_buffer.emplace_back(new_gname, meta);
                            subgoal_idx++;
                        }
                    }
                    new_gs = to_list(subgoals.begin(), subgoals.end(), new_gs);
                    list<std::pair<name, expr>> trace = to_list(trace_buffer.begin(), trace_buffer.end());
                    proof_builder pb = s.get_pb();
                    proof_builder new_pb([=](proof_map const & m, substitution const & pb_subst) {
                            proof_map new_m(m);
                            substitution new_subst;
                            for (auto const & p : trace) {
                                expr pr   = find(new_m, p.first);
                                expr meta = p.second;
                                buffer<expr> meta_args;
                                expr mvar = get_app_args(meta, meta_args);
                                unsigned i = meta_args.size();
                                while (i > 0) {
                                    --i;
                                    pr = Fun(meta_args[i], pr);
                                }
                                new_subst = new_subst.assign(mlocal_name(mvar), pr, justification());
                                new_m.erase(p.first);
                            }
                            new_m.insert(gname, new_subst.instantiate_metavars_wo_jst(P));
                            return pb(new_m, pb_subst);
                        });
                    return proof_state(s, new_gs, new_pb, new_ngen);
                });
        });
}

int mk_apply_tactic(lua_State * L) { return push_tactic(L, apply_tactic(to_expr(L, 1))); }
void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_apply_tactic,     "apply_tac");
}
}
