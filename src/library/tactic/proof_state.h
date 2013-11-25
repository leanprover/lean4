/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include "util/rc.h"
#include "util/interrupt.h"
#include "util/optional.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"

namespace lean {
typedef list<std::pair<name, goal>> goals;
class proof_state {
    struct cell {
        MK_LEAN_RC();
        goals                       m_goals;
        metavar_env                 m_menv;
        proof_builder               m_proof_builder;
        void dealloc() { delete this; }
        cell():m_rc(1) {}
        cell(goals const & gs, metavar_env const & menv, proof_builder const & p):
            m_rc(1), m_goals(gs), m_menv(menv), m_proof_builder(p) {}
    };
    cell * m_ptr;
public:
    proof_state():m_ptr(new cell()) {}
    proof_state(proof_state const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    proof_state(proof_state && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    proof_state(goals const & gs, metavar_env const & menv, proof_builder const & p):m_ptr(new cell(gs, menv, p)) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & p):m_ptr(new cell(gs, s.m_ptr->m_menv, p)) {}
    ~proof_state() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(proof_state & a, proof_state & b) { std::swap(a.m_ptr, b.m_ptr); }
    proof_state & operator=(proof_state const & s) { LEAN_COPY_REF(proof_state, s); }
    proof_state & operator=(proof_state && s) { LEAN_MOVE_REF(proof_state, s); }
    goals const & get_goals() const { lean_assert(m_ptr); return m_ptr->m_goals; }
    metavar_env const & get_menv() const { lean_assert(m_ptr); return m_ptr->m_menv; }
    proof_builder const & get_proof_builder() const { lean_assert(m_ptr); return m_ptr->m_proof_builder; }
    format pp(formatter const & fmt, options const & opts) const;
};

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
