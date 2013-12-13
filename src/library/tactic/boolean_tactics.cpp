/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/interrupt.h"
#include "kernel/builtin.h"
#include "kernel/abstract.h"
#include "kernel/occurs.h"
#include "library/basic_thms.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"

namespace lean {
tactic conj_tactic(bool all) {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            bool found = false;
            buffer<std::pair<name, goal>> new_goals_buf;
            list<std::pair<name, expr>> proof_info;
            for (auto const & p : s.get_goals()) {
                check_interrupted();
                goal const & g = p.second;
                expr const & c = g.get_conclusion();
                expr c1, c2;
                if ((all || !found) && is_and(c, c1, c2)) {
                    found = true;
                    name const & n = p.first;
                    proof_info.emplace_front(n, c);
                    new_goals_buf.emplace_back(name(n, 1), update(g, c1));
                    new_goals_buf.emplace_back(name(n, 2), update(g, c2));
                } else {
                    new_goals_buf.push_back(p);
                }
            }
            if (found) {
                proof_builder pr_builder     = s.get_proof_builder();
                proof_builder new_pr_builder = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                        proof_map new_m(m);
                        for (auto nc : proof_info) {
                            name const & n = nc.first;
                            expr const & c = nc.second;
                            new_m.insert(n, Conj(arg(c, 1), arg(c, 2), find(m, name(n, 1)), find(m, name(n, 2))));
                            new_m.erase(name(n, 1));
                            new_m.erase(name(n, 2));
                        }
                        return pr_builder(new_m, a);
                    });
                goals new_goals = to_list(new_goals_buf.begin(), new_goals_buf.end());
                return some_proof_state(s, new_goals, new_pr_builder);
            } else {
                return none_proof_state();
            }
        });
}

tactic imp_tactic(name const & H_name, bool all) {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            expr impfn = mk_implies_fn();
            bool found = false;
            list<std::tuple<name, name, expr>> proof_info;
            goals new_goals = map_goals(s, [&](name const & g_name, goal const & g) -> optional<goal> {
                    expr const & c  = g.get_conclusion();
                    expr new_h, new_c;
                    if ((all || !found) && is_implies(c, new_h, new_c)) {
                        found = true;
                        name new_h_name = g.mk_unique_hypothesis_name(H_name);
                        proof_info.emplace_front(g_name, new_h_name, c);
                        return optional<goal>(goal(add_hypothesis(new_h_name, new_h, g.get_hypotheses()), new_c));
                    } else {
                        return optional<goal>(g);
                    }
                });
            if (found) {
                proof_builder pr_builder     = s.get_proof_builder();
                proof_builder new_pr_builder = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                        proof_map new_m(m);
                        for (auto const & info : proof_info) {
                            name const & goal_name = std::get<0>(info);
                            name const & hyp_name  = std::get<1>(info);  // new hypothesis name
                            expr const & old_c     = std::get<2>(info);  // old conclusion of the form H => C
                            expr const & h         = arg(old_c, 1); // new hypothesis: antencedent of the old conclusion
                            expr const & c         = arg(old_c, 2); // new conclusion: consequent of the old conclusion
                            expr const & c_pr      = find(m, goal_name);   // proof for the new conclusion
                            new_m.insert(goal_name, Discharge(h, c, Fun(hyp_name, h, c_pr)));
                        }
                        return pr_builder(new_m, a);
                    });
                return some_proof_state(s, new_goals, new_pr_builder);
            } else {
                return none_proof_state();
            }
        });
}

tactic conj_hyp_tactic(bool all) {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            bool found = false;
            list<std::pair<name, hypotheses>> proof_info; // goal name -> expanded hypotheses
            goals new_goals = map_goals(s, [&](name const & ng, goal const & g) -> optional<goal> {
                    if (all || !found) {
                        buffer<hypothesis> new_hyp_buf;
                        hypotheses proof_info_data;
                        for (auto const & p : g.get_hypotheses()) {
                            name const & H_name = p.first;
                            expr const & H_prop = p.second;
                            expr H1, H2;
                            if ((all || !found) && is_and(H_prop, H1, H2)) {
                                found       = true;
                                proof_info_data = add_hypothesis(p, proof_info_data);
                                new_hyp_buf.emplace_back(name(H_name, 1), H1);
                                new_hyp_buf.emplace_back(name(H_name, 2), H2);
                            } else {
                                new_hyp_buf.push_back(p);
                            }
                        }
                        if (proof_info_data) {
                            proof_info.emplace_front(ng, proof_info_data);
                            return some(update(g, new_hyp_buf));
                        } else {
                            return some(g);
                        }
                    } else {
                        return some(g);
                    }
                });
            if (found) {
                proof_builder pr_builder     = s.get_proof_builder();
                proof_builder new_pr_builder = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                        proof_map new_m(m);
                        for (auto const & info : proof_info) {
                            name const & goal_name     = info.first;
                            auto const & expanded_hyps = info.second;
                            expr pr                    = find(m, goal_name); // proof for the new conclusion
                            for (auto const & H_name_prop : expanded_hyps) {
                                name const & H_name   = H_name_prop.first;
                                expr const & H_prop   = H_name_prop.second;
                                expr const & H_1      = mk_constant(name(H_name, 1));
                                expr const & H_2      = mk_constant(name(H_name, 2));
                                if (occurs(H_1, pr))
                                    pr = Let_simp(H_1, Conjunct1(arg(H_prop, 1), arg(H_prop, 2), mk_constant(H_name)), pr);
                                if (occurs(H_2, pr))
                                    pr = Let_simp(H_2, Conjunct2(arg(H_prop, 1), arg(H_prop, 2), mk_constant(H_name)), pr);
                            }
                            new_m.insert(goal_name, pr);
                        }
                        return pr_builder(new_m, a);
                    });
                return some_proof_state(s, new_goals, new_pr_builder);
            } else {
                return none_proof_state();
            }
        });
}

optional<proof_state> disj_hyp_tactic_core(name const & goal_name, name const & hyp_name, proof_state const & s) {
    buffer<std::pair<name, goal>> new_goals_buf;
    optional<expr> H;
    expr conclusion;
    for (auto const & p1 : s.get_goals()) {
        check_interrupted();
        if (p1.first == goal_name) {
            goal const & g = p1.second;
            buffer<hypothesis> new_hyp_buf1;
            buffer<hypothesis> new_hyp_buf2;
            conclusion = g.get_conclusion();
            for (auto const & p2 : g.get_hypotheses()) {
                if (p2.first == hyp_name) {
                    H = p2.second;
                    if (!is_or(*H))
                        return none_proof_state(); // tactic failed
                    new_hyp_buf1.emplace_back(p2.first, arg(*H, 1));
                    new_hyp_buf2.emplace_back(p2.first, arg(*H, 2));
                } else {
                    new_hyp_buf1.push_back(p2);
                    new_hyp_buf2.push_back(p2);
                }
            }
            if (!H)
                return none_proof_state(); // tactic failed
            new_goals_buf.emplace_back(name(goal_name, 1), update(g, new_hyp_buf1));
            new_goals_buf.emplace_back(name(goal_name, 2), update(g, new_hyp_buf2));
        } else {
            new_goals_buf.push_back(p1);
        }
    }
    if (!H)
        return none_proof_state(); // tactic failed
    goals new_gs = to_list(new_goals_buf.begin(), new_goals_buf.end());
    proof_builder pb     = s.get_proof_builder();
    expr Href = *H;
    proof_builder new_pb = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
            proof_map new_m(m);
            expr pr1 = find(m, name(goal_name, 1));
            expr pr2 = find(m, name(goal_name, 2));
            pr1 = Fun(hyp_name, arg(Href, 1), pr1);
            pr2 = Fun(hyp_name, arg(Href, 2), pr2);
            new_m.insert(goal_name, DisjCases(arg(Href, 1), arg(Href, 2), conclusion, mk_constant(hyp_name), pr1, pr2));
            new_m.erase(name(goal_name, 1));
            new_m.erase(name(goal_name, 2));
            return pb(new_m, a);
        });
    return some_proof_state(s, new_gs, new_pb);
}

tactic disj_hyp_tactic(name const & goal_name, name const & hyp_name) {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            return disj_hyp_tactic_core(goal_name, hyp_name, s);
        });
}

tactic disj_hyp_tactic(name const & hyp_name) {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            for (auto const & p1 : s.get_goals()) {
                check_interrupted();
                goal const & g = p1.second;
                for (auto const & p2 : g.get_hypotheses()) {
                    if (p2.first == hyp_name)
                        return disj_hyp_tactic_core(p1.first, hyp_name, s);
                }
            }
            return none_proof_state(); // tactic failed
        });
}

tactic disj_hyp_tactic() {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            for (auto const & p1 : s.get_goals()) {
                check_interrupted();
                goal const & g = p1.second;
                for (auto const & p2 : g.get_hypotheses()) {
                    if (is_or(p2.second))
                        return disj_hyp_tactic_core(p1.first, p2.first, s);
                }
            }
            return none_proof_state(); // tactic failed
        });
}

typedef std::pair<proof_state, proof_state> proof_state_pair;

optional<proof_state_pair> disj_tactic(proof_state const & s, name gname) {
    precision prec = s.get_precision();
    if (prec != precision::Precise && prec != precision::Over) {
        // it is pointless to apply this tactic, since it will produce UnderOver
        optional<proof_state_pair>();
    }
    buffer<std::pair<name, goal>> new_goals_buf1, new_goals_buf2;
    optional<expr> conclusion;
    for (auto const & p : s.get_goals()) {
        check_interrupted();
        goal const & g = p.second;
        expr const & c = g.get_conclusion();
        if (!conclusion && ((gname.is_anonymous() && is_or(c)) || p.first == gname)) {
            gname = p.first;
            conclusion = c;
            expr c1, c2;
            if (is_or(c, c1, c2)) {
                new_goals_buf1.emplace_back(gname, update(g, c1));
                new_goals_buf2.emplace_back(gname, update(g, c2));
            } else {
                return optional<proof_state_pair>(); // failed
            }
        } else {
            new_goals_buf1.push_back(p);
            new_goals_buf2.push_back(p);
        }
    }
    if (!conclusion) {
        return optional<proof_state_pair>(); // failed
    } else {
        goals new_gs1 = to_list(new_goals_buf1.begin(), new_goals_buf1.end());
        goals new_gs2 = to_list(new_goals_buf2.begin(), new_goals_buf2.end());
        proof_builder pb     = s.get_proof_builder();
        proof_builder new_pb1 = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                proof_map new_m(m);
                new_m.insert(gname, Disj1(arg(*conclusion, 1), arg(*conclusion, 2), find(m, gname)));
                return pb(new_m, a);
            });
        proof_builder new_pb2 = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                proof_map new_m(m);
                new_m.insert(gname, Disj2(arg(*conclusion, 2), arg(*conclusion, 1), find(m, gname)));
                return pb(new_m, a);
            });
        proof_state s1(precision::Over, new_gs1, s.get_menv(), new_pb1, s.get_cex_builder());
        proof_state s2(precision::Over, new_gs2, s.get_menv(), new_pb2, s.get_cex_builder());
        return some(mk_pair(s1, s2));
    }
}

proof_state_seq disj_tactic_core(proof_state const & s, name const & gname) {
    return mk_proof_state_seq([=]() {
            auto p = disj_tactic(s, gname);
            if (p) {
                return some(mk_pair(p->first, proof_state_seq(p->second)));
            } else {
                return proof_state_seq::maybe_pair();
            }
        });
}

tactic disj_tactic(name const & gname) {
    return mk_tactic([=](ro_environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            return disj_tactic_core(s, gname);
        });
}

tactic disj_tactic() {
    return disj_tactic(name());
}

tactic disj_tactic(unsigned i) {
    return mk_tactic([=](ro_environment const &, io_state const &, proof_state const & s) -> proof_state_seq {
            if (optional<name> n = s.get_ith_goal_name(i))
                return disj_tactic_core(s, *n);
            else
                return proof_state_seq();
        });
}

tactic absurd_tactic() {
    return mk_tactic01([](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            list<std::pair<name, expr>> proofs;
            goals new_gs = map_goals(s, [&](name const & gname, goal const & g) -> optional<goal> {
                    expr const & c  = g.get_conclusion();
                    for (auto const & p1 : g.get_hypotheses()) {
                        check_interrupted();
                        expr a;
                        if (is_not(p1.second, a)) {
                            for (auto const & p2 : g.get_hypotheses()) {
                                if (p2.second == a) {
                                    expr pr = AbsurdImpAny(a, c, mk_constant(p2.first), mk_constant(p1.first));
                                    proofs.emplace_front(gname, pr);
                                    return optional<goal>(); // remove goal
                                }
                            }
                        }
                    }
                    return some(g); // keep goal
                });
            if (empty(proofs))
                return none_proof_state(); // tactic failed
            proof_builder new_pb = add_proofs(s.get_proof_builder(), proofs);
            return some(proof_state(s, new_gs, new_pb));
        });
}

static int mk_conj_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_tactic(L, conj_tactic(nargs == 0 ? true : lua_toboolean(L, 1)));
}

static int mk_imp_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_tactic(L, imp_tactic(nargs >= 1 ? to_name_ext(L, 1) : name("H"), nargs == 2 ? lua_toboolean(L, 2) : true));
}

static int mk_conj_hyp_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_tactic(L, conj_hyp_tactic(nargs == 0 ? true : lua_toboolean(L, 1)));
}

static int mk_disj_hyp_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_tactic(L, disj_hyp_tactic());
    else if (nargs == 1)
        return push_tactic(L, disj_hyp_tactic(to_name_ext(L, 1)));
    else
        return push_tactic(L, disj_hyp_tactic(to_name_ext(L, 1), to_name_ext(L, 2)));
}

static int mk_disj_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_tactic(L, disj_tactic());
    else if (lua_isnumber(L, 1))
        return push_tactic(L, disj_tactic(lua_tointeger(L, 1)));
    else
        return push_tactic(L, disj_tactic(to_name_ext(L, 1)));
}

static int mk_absurd_tactic(lua_State * L) {
    return push_tactic(L, absurd_tactic());
}

void open_boolean_tactics(lua_State * L) {
    SET_GLOBAL_FUN(mk_conj_tactic,     "conj_tac");
    SET_GLOBAL_FUN(mk_imp_tactic,      "imp_tac");
    SET_GLOBAL_FUN(mk_conj_hyp_tactic, "conj_hyp_tac");
    SET_GLOBAL_FUN(mk_disj_hyp_tactic, "disj_hyp_tac");
    SET_GLOBAL_FUN(mk_disj_tactic,     "disj_tac");
    SET_GLOBAL_FUN(mk_absurd_tactic,   "absurd_tac");
}
}
