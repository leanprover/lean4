/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/interrupt.h"
#include "kernel/builtin.h"
#include "kernel/abstract.h"
#include "library/basic_thms.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"

namespace lean {
bool is_app_of(expr const & e, expr const & f) {
    return is_app(e) && arg(e, 0) == f;
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
                if ((all || !found) && is_app_of(c, andfn)) {
                    found = true;
                    name const & n = p.first;
                    proof_info.emplace_front(n, c);
                    new_goals_buf.emplace_back(name(n, 1), goal(g.get_hypotheses(), arg(c, 1)));
                    new_goals_buf.emplace_back(name(n, 2), goal(g.get_hypotheses(), arg(c, 2)));
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
                        }
                        return p(new_m, env, a);
                    });
                goals new_goals = to_list(new_goals_buf.begin(), new_goals_buf.end());
                return some(proof_state(s, new_goals, new_p));
            } else {
                return optional<proof_state>();
            }
        });
}
tactic imp_tactic(name const & H_name, bool all) {
    return mk_tactic01([=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            expr impfn = mk_implies_fn();
            bool found = false;
            list<std::tuple<name, name, expr>> proof_info;
            goals new_goals = map_goals(s, [&](name const & ng, goal const & g) -> goal {
                    expr const & c  = g.get_conclusion();
                    if ((all || !found) && is_app_of(c, impfn)) {
                        found = true;
                        name new_hn = g.mk_unique_hypothesis_name(H_name);
                        proof_info.emplace_front(ng, new_hn, c);
                        expr new_h  = arg(c, 1);
                        expr new_c  = arg(c, 2);
                        return goal(cons(mk_pair(new_hn, new_h), g.get_hypotheses()), new_c);
                    } else {
                        return g;
                    }
                });
            if (found) {
                proof_builder p     = s.get_proof_builder();
                proof_builder new_p = mk_proof_builder([=](proof_map const & m, environment const & env, assignment const & a) -> expr {
                        proof_map new_m(m);
                        for (auto info : proof_info) {
                            name const & gn     = std::get<0>(info);  // goal name
                            name const & hn     = std::get<1>(info);  // new hypothesis name
                            expr const & old_c  = std::get<2>(info);  // old conclusion of the form H => C
                            expr const & h      = arg(old_c, 1); // new hypothesis: antencedent of the old conclusion
                            expr const & c      = arg(old_c, 2); // new conclusion: consequent of the old conclusion
                            expr const & c_pr   = find(m, gn);   // proof for the new conclusion
                            new_m.insert(gn, Discharge(h, c, Fun(hn, h, c_pr)));
                        }
                        return p(new_m, env, a);
                    });
                return some(proof_state(s, new_goals, new_p));
            } else {
                return optional<proof_state>();
            }
        });
}
}
