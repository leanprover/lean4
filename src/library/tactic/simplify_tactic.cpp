/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/buffer.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/kernel.h"
#include "library/simplifier/simplifier.h"
#include "library/tactic/tactic.h"

#ifndef LEAN_SIMP_TAC_ASSUMPTIONS
#define LEAN_SIMP_TAC_ASSUMPTIONS true
#endif

namespace lean {
static name g_simp_tac_assumptions {"simp_tac", "assumptions"};
RegisterBoolOption(g_simp_tac_assumptions, LEAN_SIMP_TAC_ASSUMPTIONS, "(simplifier tactic) use goal assumptions as rewrite rules");
bool get_simp_tac_assumptions(options const & opts) { return opts.get_bool(g_simp_tac_assumptions, LEAN_SIMP_TAC_ASSUMPTIONS); }

static name g_assumption("assump");

static optional<proof_state> simplify_tactic(ro_environment const & env, io_state const & ios, proof_state const & s,
                                             unsigned num_ns, name const * ns, options const & extra_opts,
                                             std::shared_ptr<simplifier_monitor> const & monitor) {
    if (empty(s.get_goals()))
        return none_proof_state();
    options opts = join(extra_opts, ios.get_options());

    auto const & p              = head(s.get_goals());
    name const & gname          = p.first;
    goal const & g              = p.second;
    ro_metavar_env const & menv = s.get_menv();
    type_checker tc(env);

    bool use_assumptions = get_simp_tac_assumptions(opts);
    buffer<rewrite_rule_set> rule_sets;
    if (use_assumptions) {
        rule_sets.push_back(rewrite_rule_set(env));
        rewrite_rule_set & rs = rule_sets[0];
        for (auto const & p : g.get_hypotheses()) {
            if (tc.is_proposition(p.second, context(), menv)) {
                expr H = mk_constant(p.first, p.second);
                rs.insert(g_assumption, p.second, H, some_ro_menv(menv));
            }
        }
    }
    for (unsigned i = 0; i < num_ns; i++) {
        rule_sets.push_back(get_rewrite_rule_set(env, ns[i]));
    }

    expr conclusion         = g.get_conclusion();
    auto r                  = simplify(conclusion, env, opts, rule_sets.size(), rule_sets.data(), some_ro_menv(menv), monitor);
    expr new_conclusion     = r.get_expr();
    if (new_conclusion == g.get_conclusion())
        return optional<proof_state>(s);
    expr eq_proof;
    if (!r.get_proof()) {
        // TODO(Leo): we should create a "by simplifier" proof
        // For now, we just fail
        return none_proof_state();
    } else {
        eq_proof = *r.get_proof();
    }
    if (r.is_heq_proof())
        eq_proof = mk_to_eq_th(Bool, conclusion, new_conclusion, eq_proof);
    bool solved          = is_true(new_conclusion);
    goals rest_gs        = tail(s.get_goals());
    goals new_gs;
    if (solved)
        new_gs = rest_gs;
    else
        new_gs = goals(mk_pair(gname, update(g, new_conclusion)), rest_gs);
    proof_builder pb     = s.get_proof_builder();
    proof_builder new_pb = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
            proof_map new_m(m);
            if (solved)
                new_m.insert(gname, mk_eqt_elim_th(conclusion, eq_proof));
            else
                new_m.insert(gname, mk_eqmpr_th(conclusion, new_conclusion, eq_proof, find(m, gname)));
            return pb(new_m, a);
        });
    return some(proof_state(s, new_gs, new_pb));
}

tactic simplify_tactic(unsigned num_ns, name const * ns, options const & opts, std::shared_ptr<simplifier_monitor> const & monitor) {
    std::vector<name> names(ns, ns + num_ns);
    return mk_tactic01([=](ro_environment const & env, io_state const & ios, proof_state const & s) -> optional<proof_state> {
            return simplify_tactic(env, ios, s, names.size(), names.data(), opts, monitor);
        });
}

static int mk_simplify_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_tactic(L, simplify_tactic(1, &get_default_rewrite_rule_set_id(), options(), get_global_simplifier_monitor(L)));
    } else if (nargs == 1 && is_options(L, 1)) {
        return push_tactic(L, simplify_tactic(1, &get_default_rewrite_rule_set_id(), to_options(L, 1), get_global_simplifier_monitor(L)));
    } else {
        buffer<name> rs;
        if (lua_isstring(L, 1)) {
            rs.push_back(lua_tostring(L, 1));
        } else if (lua_istable(L, 1)) {
            int n = objlen(L, 1);
            for (int i = 1; i <= n; i++) {
                lua_rawgeti(L, 1, i);
                rs.push_back(to_name_ext(L, -1));
                lua_pop(L, 1);
            }
        } else {
            rs.push_back(to_name_ext(L, 1));
        }
        options opts;
        if (nargs >= 2)
            opts = to_options(L, 2);
        return push_tactic(L, simplify_tactic(rs.size(), rs.data(), opts, get_simplifier_monitor(L, 3)));
    }
}

void open_simplify_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_simplify_tactic, "simp_tac");
}
}
