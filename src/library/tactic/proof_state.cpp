/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/tactic/tactic_exception.h"
#include "library/tactic/proof_state.h"

namespace lean {
format proof_state::pp(formatter const & fmt, options const & opts) const {
    format r;
    bool first = true;
    for (auto const & p : m_goals) {
        if (first)
            first = false;
        else
            r += line();
        r += group(format{format(p.first), colon(), line(), p.second.pp(fmt, opts)});
    }
    return r;
}

void swap(proof_state & s1, proof_state & s2) {
    swap(s1.m_goals, s2.m_goals);
    swap(s1.m_menv, s2.m_menv);
    swap(s1.m_proof_builder, s2.m_proof_builder);
    swap(s1.m_justification_builder, s2.m_justification_builder);
}

static name g_main("main");

proof_state to_proof_state(environment const & env, context const & ctx, expr const & t) {
    auto gfn         = to_goal(env, ctx, t);
    goal g           = gfn.first;
    goal_proof_fn fn = gfn.second;
    proof_builder p  = mk_proof_builder(
        [=](proof_map const & m, environment const &, assignment const &) -> expr {
            expr p = find(m, g_main);
            if (!p)
                throw tactic_exception(sstream() << "failed to find proof for '" << g_main << "' goal");
            return fn(p);
        });
    justification_builder j = mk_justification_builder(
        [](name const & n, justification const & j, environment const &, assignment const &) -> justification {
            if (n != g_main)
                throw tactic_exception(sstream() << "unknown goal name '" << n << "'");
            return j;
        });
    return proof_state(goals(mk_pair(g_main, g)), metavar_env(), p, j);
}
}
