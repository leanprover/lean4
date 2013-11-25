/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/interrupt.h"
#include "util/optional.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"

namespace lean {
typedef list<std::pair<name, goal>> goals;
class proof_state {
    goals                       m_goals;
    metavar_env                 m_menv;
    proof_builder               m_proof_builder;
public:
    proof_state() {}
    proof_state(list<std::pair<name, goal>> const & gs, metavar_env const & menv, proof_builder const & p):
        m_goals(gs), m_menv(menv), m_proof_builder(p) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & p):
        m_goals(gs), m_menv(s.m_menv), m_proof_builder(p) {}
    friend void swap(proof_state & s1, proof_state & s2);
    list<std::pair<name, goal>> const & get_goals() const { return m_goals; }
    metavar_env const & get_menv() const { return m_menv; }
    proof_builder const & get_proof_builder() const { return m_proof_builder; }
    format pp(formatter const & fmt, options const & opts) const;
};
void swap(proof_state & s1, proof_state & s2);

proof_state to_proof_state(environment const & env, context const & ctx, expr const & t);

inline optional<proof_state> some_proof_state(proof_state const & s, goals const & gs, proof_builder const & p) {
    return some(proof_state(s, gs, p));
}
inline optional<proof_state> none_proof_state() { return optional<proof_state> (); }

template<typename F>
goals map_goals(proof_state const & s, F && f) {
    return map_filter(s.get_goals(), [=](std::pair<name, goal> const & in, std::pair<name, goal> & out) -> bool {
            check_interrupted();
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
