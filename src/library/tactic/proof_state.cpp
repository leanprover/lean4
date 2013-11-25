/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/tactic/proof_state.h"

namespace lean {
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

static name g_main("main");

proof_state to_proof_state(environment const & env, context const & ctx, expr const & t) {
    auto gfn                 = to_goal(env, ctx, t);
    goal g                   = gfn.first;
    goal_proof_fn fn         = gfn.second;
    proof_builder pr_builder = mk_proof_builder(
        [=](proof_map const & m, assignment const &) -> expr {
            expr p = find(m, g_main);
            if (!p)
                throw exception(sstream() << "failed to find proof for '" << g_main << "' goal");
            return fn(p);
        });
    return proof_state(goals(mk_pair(g_main, g)), metavar_env(), pr_builder);
}
}
