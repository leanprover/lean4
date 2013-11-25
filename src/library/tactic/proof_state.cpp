/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/builtin.h"
#include "library/tactic/proof_state.h"

namespace lean {
precision mk_union(precision p1, precision p2) {
    if (p1 == p2) return p1;
    else if (p1 == precision::Precise) return p2;
    else if (p2 == precision::Precise) return p1;
    else return precision::UnderOver;
}

bool trust_proof(precision p) {
    return p == precision::Precise || p == precision::Over;
}

bool trust_cex(precision p) {
    return p == precision::Precise || p == precision::Under;
}

format proof_state::pp(formatter const & fmt, options const & opts) const {
    format r;
    bool first = true;
    for (auto const & p : get_goals()) {
        if (first)
            first = false;
        else
            r += line();
        r += p.second.pp(fmt, opts);
    }
    return r;
}

bool proof_state::is_proof_final_state() const {
    return empty(get_goals()) && trust_proof(get_precision());
}

bool proof_state::is_cex_final_state() const {
    if (length(get_goals()) == 1 && trust_cex(get_precision())) {
        goal const & g = head(get_goals()).second;
        return is_false(g.get_conclusion()) && empty(g.get_hypotheses());
    } else {
        return false;
    }
}

static name g_main("main");

proof_state to_proof_state(environment const & env, context const & ctx, expr const & t) {
    auto gfn                 = to_goal(env, ctx, t);
    goal g                   = gfn.first;
    goal_proof_fn fn         = gfn.second;
    proof_builder pr_builder = mk_proof_builder(
        [=](proof_map const & m, assignment const &) -> expr {
            return fn(find(m, g_main));
        });
    cex_builder cex_builder = mk_cex_builder(
        [](name const & n, optional<counterexample> const & cex, assignment const &) -> counterexample {
            if (n != g_main || !cex)
                throw exception(sstream() << "failed to build counterexample for '" << g_main << "' goal");
            return *cex;
        });
    return proof_state(goals(mk_pair(g_main, g)), metavar_env(), pr_builder, cex_builder);
}
}
