/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/justification_builder.h"

namespace lean {
typedef list<std::pair<name, goal>> goals;
class proof_state {
    goals                       m_goals;
    metavar_env                 m_menv;
    proof_builder               m_proof_builder;
    justification_builder       m_justification_builder;
public:
    proof_state() {}
    proof_state(list<std::pair<name, goal>> const & gs, metavar_env const & menv, proof_builder const & p, justification_builder const & j):
        m_goals(gs), m_menv(menv), m_proof_builder(p), m_justification_builder(j) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & p):
        m_goals(gs), m_menv(s.m_menv), m_proof_builder(p), m_justification_builder(s.m_justification_builder) {}
    friend void swap(proof_state & s1, proof_state & s2);
    list<std::pair<name, goal>> const & get_goals() const { return m_goals; }
    metavar_env const & get_menv() const { return m_menv; }
    proof_builder const & get_proof_builder() const { return m_proof_builder; }
    justification_builder const & get_justification_builder() const { return m_justification_builder; }
};
void swap(proof_state & s1, proof_state & s2);

proof_state to_proof_state(environment const & env, context const & ctx, expr const & t);

template<typename F>
goals map_goals(proof_state const & s, F && f) {
    return map_filter(s.get_goals(), [=](std::pair<name, goal> const & in, std::pair<name, goal> & out) -> bool {
            goal new_goal = f(in.first, in.second);
            if (new_goal) {
                out.first  = in.first;
                out.second = new_goal;
                return true;
            } else {
                return false;
            }
        });
}
}
