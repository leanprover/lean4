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
bool is_app_of(expr const & e, expr const & f) {
    return is_app(e) && arg(e, 0) == f;
}

bool is_app_of(expr const & e, expr const & f, expr & arg1, expr & arg2) {
    if (is_app_of(e, f)) {
        arg1 = arg(e, 1);
        arg2 = arg(e, 2);
        return true;
    } else {
        return false;
    }
}

tactic conj_tactic(bool all) {
    return mk_tactic01([=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            expr andfn = mk_and_fn();
            bool found = false;
            buffer<std::pair<name, goal>> new_goals_buf;
            list<std::pair<name, expr>> proof_info;
            for (auto const & p : s.get_goals()) {
                check_interrupted();
                goal const & g = p.second;
                expr const & c = g.get_conclusion();
                expr c1, c2;
                if ((all || !found) && is_app_of(c, andfn, c1, c2)) {
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
                proof_builder p     = s.get_proof_builder();
                proof_builder new_p = mk_proof_builder([=](proof_map const & m, environment const & env, assignment const & a) -> expr {
                        proof_map new_m(m);
                        for (auto nc : proof_info) {
                            name const & n = nc.first;
                            expr const & c = nc.second;
                            new_m.insert(n, Conj(arg(c, 1), arg(c, 2), find(m, name(n, 1)), find(m, name(n, 2))));
                            new_m.erase(name(n, 1));
                            new_m.erase(name(n, 2));
                        }
                        return p(new_m, env, a);
                    });
                goals new_goals = to_list(new_goals_buf.begin(), new_goals_buf.end());
                return some_proof_state(s, new_goals, new_p);
            } else {
                return none_proof_state();
            }
        });
}

tactic imp_tactic(name const & H_name, bool all) {
    return mk_tactic01([=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            expr impfn = mk_implies_fn();
            bool found = false;
            list<std::tuple<name, name, expr>> proof_info;
            goals new_goals = map_goals(s, [&](name const & g_name, goal const & g) -> goal {
                    expr const & c  = g.get_conclusion();
                    expr new_h, new_c;
                    if ((all || !found) && is_app_of(c, impfn, new_h, new_c)) {
                        found = true;
                        name new_h_name = g.mk_unique_hypothesis_name(H_name);
                        proof_info.emplace_front(g_name, new_h_name, c);
                        return goal(add_hypothesis(new_h_name, new_h, g.get_hypotheses()), new_c);
                    } else {
                        return g;
                    }
                });
            if (found) {
                proof_builder p     = s.get_proof_builder();
                proof_builder new_p = mk_proof_builder([=](proof_map const & m, environment const & env, assignment const & a) -> expr {
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
                        return p(new_m, env, a);
                    });
                return some_proof_state(s, new_goals, new_p);
            } else {
                return none_proof_state();
            }
        });
}

tactic conj_hyp_tactic(bool all) {
    return mk_tactic01([=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            expr andfn = mk_and_fn();
            bool found = false;
            list<std::pair<name, hypotheses>> proof_info; // goal name -> expanded hypotheses
            goals new_goals = map_goals(s, [&](name const & ng, goal const & g) -> goal {
                    if (all || !found) {
                        buffer<hypothesis> new_hyp_buf;
                        hypotheses proof_info_data;
                        for (auto const & p : g.get_hypotheses()) {
                            name const & H_name = p.first;
                            expr const & H_prop = p.second;
                            expr H1, H2;
                            if ((all || !found) && is_app_of(H_prop, andfn, H1, H2)) {
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
                            return update(g, new_hyp_buf);
                        } else {
                            return g;
                        }
                    } else {
                        return g;
                    }
                });
            if (found) {
                proof_builder p     = s.get_proof_builder();
                proof_builder new_p = mk_proof_builder([=](proof_map const & m, environment const & env, assignment const & a) -> expr {
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
                                    pr = Let(H_1, Conjunct1(arg(H_prop, 1), arg(H_prop, 2), mk_constant(H_name)), pr);
                                if (occurs(H_2, pr))
                                    pr = Let(H_2, Conjunct2(arg(H_prop, 1), arg(H_prop, 2), mk_constant(H_name)), pr);
                            }
                            new_m.insert(goal_name, pr);
                        }
                        return p(new_m, env, a);
                    });
                return some_proof_state(s, new_goals, new_p);
            } else {
                return none_proof_state();
            }
        });
}
}
