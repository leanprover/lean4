/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include "util/lua.h"
#include "util/optional.h"
#include "util/name_set.h"
#include "library/tactic/goal.h"

namespace lean {
typedef list<goal> goals;
class proof_state {
    goals            m_goals;
    substitution     m_subst;
    name_generator   m_ngen;
    // The following term is of the form (?m l_1 ... l_n), it captures the
    // metavariable this proof state is trying to synthesize, and
    // the context [l_1, ..., l_n]. The context is important because it allows
    // us to "reinterpret" an expression in this context.
    expr             m_inital;
public:
    proof_state(goals const & gs, substitution const & s, name_generator const & ngen, expr const & ini):
        m_goals(gs), m_subst(s), m_ngen(ngen), m_inital(ini) {}
    proof_state(proof_state const & s, goals const & gs, substitution const & subst, name_generator const & ngen):
        proof_state(gs, subst, ngen, s.m_inital) {}
    proof_state(proof_state const & s, goals const & gs, substitution const & subst):proof_state(s, gs, subst, s.m_ngen) {}
    proof_state(proof_state const & s, goals const & gs):proof_state(s, gs, s.m_subst) {}
    proof_state(proof_state const & s, name_generator const & ngen):proof_state(s.m_goals, s.m_subst, ngen, s.m_inital) {}

    goals const & get_goals() const { return m_goals; }
    substitution const & get_subst() const { return m_subst; }
    name_generator const & get_ngen() const { return m_ngen; }
    expr const & get_initial() const { return m_inital; }

    /** \brief Return true iff this state does not have any goals left */
    bool is_final_state() const { return empty(m_goals); }
    format pp(environment const & env, formatter const & fmt, options const & opts) const;
};

inline optional<proof_state> some_proof_state(proof_state const & s) { return some(s); }
inline optional<proof_state> none_proof_state() { return optional<proof_state> (); }

/** \brief Create a proof state for a metavariable \c mvar */
proof_state to_proof_state(expr const & mvar, name_generator ngen);
proof_state to_proof_state(expr const & mvar);

goals map_goals(proof_state const & s, std::function<optional<goal>(goal const & g)> f);
io_state_stream const & operator<<(io_state_stream const & out, proof_state const & s);

UDATA_DEFS_CORE(goals)
UDATA_DEFS(proof_state)
void open_proof_state(lua_State * L);
}
