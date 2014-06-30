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
#include "library/tactic/proof_builder.h"

namespace lean {
typedef std::pair<name, goal> named_goal;
typedef list<named_goal> goals;
/** \brief Return the name of the i-th goal, return none if i == 0 or i > size(g) */
optional<name> get_ith_goal_name(goals const & gs, unsigned i);

class proof_state {
    goals            m_goals;
    proof_builder    m_proof_builder;
    name_generator   m_ngen;
    list<expr>       m_init_locals;
public:
    proof_state(goals const & gs, proof_builder const & pb, name_generator const & ngen, list<expr> const & ls = list<expr>()):
        m_goals(gs), m_proof_builder(pb), m_ngen(ngen), m_init_locals(ls) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & pb, name_generator const & ngen):
        proof_state(gs, pb, ngen, s.m_init_locals) {}
    proof_state(proof_state const & s, goals const & gs, proof_builder const & pb):proof_state(s, gs, pb, s.m_ngen) {}
    proof_state(proof_state const & s, goals const & gs):proof_state(s, gs, s.m_proof_builder) {}
    proof_state(proof_state const & s, name_generator const & ngen):
        proof_state(s.m_goals, s.m_proof_builder, ngen, s.m_init_locals) {}
    goals const & get_goals() const { return m_goals; }
    proof_builder const & get_pb() const { return m_proof_builder; }
    name_generator const & ngen() const { return m_ngen; }
    list<expr> const & get_init_locals() const { return m_init_locals; }
    /** \brief Return true iff this state does not have any goals left */
    bool is_final_state() const { return empty(m_goals); }
    /** \brief Store in \c r the goal names */
    void get_goal_names(name_set & r) const;
    optional<name> get_ith_goal_name(unsigned i) const { return ::lean::get_ith_goal_name(get_goals(), i); }
    format pp(environment const & env, formatter const & fmt, options const & opts) const;
};

inline optional<proof_state> some_proof_state(proof_state const & s) { return some(s); }
inline optional<proof_state> none_proof_state() { return optional<proof_state> (); }

/** \brief Create a proof state for a metavariable \c mvar */
proof_state to_proof_state(expr const & mvar, name_generator const & ngen);
proof_state to_proof_state(expr const & mvar);
/**
    \brief Similar to the previous \c to_proof_state functions, but when \c opts contains tactic.minimize_context, and
    Type.{0} in \c env is impredicative, then only hypothesis that are not prositions are marked as "contextual".
*/
proof_state to_proof_state(environment const & env, expr const & mvar, name_generator const & ngen, options const & opts = options());
proof_state to_proof_state(environment const & env, expr const & mvar, options const & opts = options());

/** \brief Try to extract a proof from the given proof state */
optional<expr> to_proof(proof_state const & s);

goals map_goals(proof_state const & s, std::function<optional<goal>(name const & gn, goal const & g)> f);
io_state_stream const & operator<<(io_state_stream const & out, proof_state const & s);

UDATA_DEFS_CORE(goals)
UDATA_DEFS(proof_state)
void open_proof_state(lua_State * L);
}
