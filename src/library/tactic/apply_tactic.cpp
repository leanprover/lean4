/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "library/fo_unify.h"
#include "library/kernel_bindings.h"
#include "library/type_inferer.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
static name g_tmp_mvar_name = name::mk_internal_unique_name();

static optional<proof_state> apply_tactic(environment const & env, proof_state const & s,
                                          expr const & th, expr const & th_type, bool all) {
    precision prec = s.get_precision();
    if (prec != precision::Precise && prec != precision::Over) {
        // it is pointless to apply this tactic, since it will produce UnderOver
        return none_proof_state();
    }
    unsigned num = 0;
    expr th_type_c = th_type;
    while (is_pi(th_type_c)) {
        num++;
        th_type_c = abst_body(th_type_c);
    }
    buffer<expr> mvars;
    for (unsigned i = 0; i < num; i++)
        mvars.push_back(mk_metavar(name(g_tmp_mvar_name, i)));
    th_type_c = instantiate_with_closed_relaxed(th_type_c, mvars.size(), mvars.data());
    bool found = false;
    buffer<std::pair<name, goal>> new_goals_buf;
    // The proof is based on an application of th.
    // There are two kinds of arguments:
    //    1) regular arguments computed using unification.
    //    2) propostions that generate new subgoals.
    // We use a pair to simulate this "union" type.
    typedef list<std::pair<expr, name>> arg_list;
    // We may solve more than one goal.
    // We store the solved goals using a list of pairs
    // name, args. Where the 'name' is the name of the solved goal.
    type_inferer inferer(env);
    metavar_env new_menv = s.get_menv();
    list<std::pair<name, arg_list>> proof_info;
    for (auto const & p : s.get_goals()) {
        check_interrupted();
        if (all || !found) {
            name const & gname = p.first;
            goal const & g     = p.second;
            expr const & c     = g.get_conclusion();
            optional<substitution> subst = fo_unify(th_type_c, c);
            if (subst) {
                found = true;
                th_type_c = th_type;
                arg_list l;
                unsigned new_goal_idx = 1;
                for (auto const & mvar : mvars) {
                    expr mvar_sol = apply(*subst, mvar);
                    if (mvar_sol != mvar) {
                        l.emplace_front(mvar_sol, name());
                        th_type_c = instantiate(abst_body(th_type_c), mvar_sol);
                    } else {
                        if (inferer.is_proposition(abst_domain(th_type_c), context(), &new_menv)) {
                            name new_gname(gname, new_goal_idx);
                            new_goal_idx++;
                            l.emplace_front(expr(), new_gname);
                            new_goals_buf.emplace_back(new_gname, update(g, abst_domain(th_type_c)));
                            th_type_c = instantiate(abst_body(th_type_c), mk_constant(new_gname, abst_domain(th_type_c)));
                        } else {
                            // we have to create a new metavar in menv
                            // since we do not have a substitution for mvar, and
                            // it is not a proposition
                            expr new_m = new_menv.mk_metavar(context(), abst_domain(th_type_c));
                            l.emplace_front(new_m, name());
                            // we use instantiate_with_closed_relaxed because we do not want
                            // to introduce a lift operator in the new_m
                            th_type_c = instantiate_with_closed_relaxed(abst_body(th_type_c), 1, &new_m);
                        }
                    }
                }
                proof_info.emplace_front(gname, l);
            } else {
                new_goals_buf.push_back(p);
            }
        } else {
            new_goals_buf.push_back(p);
        }
    }
    if (found) {
        proof_builder pb     = s.get_proof_builder();
        proof_builder new_pb = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                proof_map new_m(m);
                for (auto const & p1 : proof_info) {
                    name const & gname = p1.first;
                    arg_list const & l = p1.second;
                    buffer<expr> args;
                    args.push_back(th);
                    for (auto const & p2 : l) {
                        expr const & arg = p2.first;
                        if (arg) {
                            // TODO(Leo): decide if we instantiate the metavars in the end or not.
                            args.push_back(arg);
                        } else {
                            name const & subgoal_name = p2.second;
                            args.push_back(find(m, subgoal_name));
                            new_m.erase(subgoal_name);
                        }
                    }
                    std::reverse(args.begin() + 1, args.end());
                    new_m.insert(gname, mk_app(args));
                }
                return pb(new_m, a);
            });
        goals new_gs = to_list(new_goals_buf.begin(), new_goals_buf.end());
        return some(proof_state(precision::Over, new_gs, new_menv, new_pb, s.get_cex_builder()));
    } else {
        return none_proof_state();
    }
}

tactic apply_tactic(expr const & th, expr const & th_type, bool all) {
    return mk_tactic01([=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            return apply_tactic(env, s, th, th_type, all);
        });
}

tactic apply_tactic(name const & th_name, bool all) {
    return mk_tactic01([=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            object const & obj = env.find_object(th_name);
            if (obj && (obj.is_theorem() || obj.is_axiom()))
                return apply_tactic(env, s, mk_constant(th_name), obj.get_type(), all);
            else
                return none_proof_state();
        });
}

int mk_apply_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_tactic(L, apply_tactic(to_name_ext(L, 1), nargs >= 2 ? lua_toboolean(L, 2) : true));
}

void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_apply_tactic,     "apply_tac");
}
}
