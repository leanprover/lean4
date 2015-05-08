/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include <functional>
#include "util/lua.h"
#include "util/optional.h"
#include "util/name_set.h"
#include "kernel/metavar.h"
#include "library/tactic/goal.h"

namespace lean {
typedef list<goal> goals;
class proof_state {
    goals            m_goals;
    substitution     m_subst;
    name_generator   m_ngen;
    constraints      m_postponed;
    bool             m_report_failure;

    format pp_core(std::function<formatter()> const & mk_fmt, options const & opts) const;

public:
    proof_state(goals const & gs, substitution const & s, name_generator const & ngen, constraints const & postponed,
                bool report_failure = true);
    proof_state(proof_state const & s, goals const & gs, substitution const & subst, name_generator const & ngen,
                constraints const & postponed):
        proof_state(gs, subst, ngen, postponed, s.report_failure()) {}
    proof_state(proof_state const & s, goals const & gs, substitution const & subst, name_generator const & ngen):
        proof_state(gs, subst, ngen, s.m_postponed, s.report_failure()) {}
    proof_state(proof_state const & s, goals const & gs, substitution const & subst):
        proof_state(s, gs, subst, s.m_ngen) {}
    proof_state(proof_state const & s, goals const & gs, name_generator const & ngen):
        proof_state(s, gs, s.m_subst, ngen) {}
    proof_state(proof_state const & s, goals const & gs):
        proof_state(s, gs, s.m_subst) {}
    proof_state(proof_state const & s, substitution const & subst, name_generator const & ngen,
                constraints const & postponed):
        proof_state(s.m_goals, subst, ngen, postponed, s.report_failure()) {}
    proof_state(proof_state const & s, name_generator const & ngen, constraints const & postponed):
        proof_state(s, s.m_goals, s.m_subst, ngen, postponed) {}
    proof_state(proof_state const & s, substitution const & subst, name_generator const & ngen):
        proof_state(s, s.m_goals, subst, ngen, s.m_postponed) {}
    proof_state(proof_state const & s, name_generator const & ngen):
        proof_state(s, ngen, s.m_postponed) {}
    proof_state(proof_state const & s, substitution const & subst):
        proof_state(s, subst, s.m_ngen) {}

    proof_state update_report_failure(bool f) const {
        return m_report_failure == f ? *this : proof_state(m_goals, m_subst, m_ngen, m_postponed, f);
    }

    goals const & get_goals() const { return m_goals; }
    substitution const & get_subst() const { return m_subst; }
    name_generator const & get_ngen() const { return m_ngen; }
    constraints const & get_postponed() const { return m_postponed; }
    bool report_failure() const { return m_report_failure; }

    /** \brief Return true iff this state does not have any goals left */
    bool is_final_state() const { return empty(m_goals); }

    /** \remark This pretty printing method creates a fresh formatter object for each goal.
        Some format objects "purify" local constant names by renaming.
        The local constants in different goals are independent of each other.
        So, this trick/hack avoids "unwanted purification".
    */
    format pp(environment const & env, io_state const & ios) const;
    format pp(formatter const & fmt) const;
};

/** \brief Apply substitution stored in \c s to main goal */
proof_state apply_substitution(proof_state const & s);

inline optional<proof_state> some_proof_state(proof_state const & s) { return some(s); }
inline optional<proof_state> none_proof_state() { return optional<proof_state> (); }

proof_state to_proof_state(expr const & meta, expr const & type, substitution const & subst, name_generator ngen);
proof_state to_proof_state(expr const & meta, expr const & type, name_generator ngen);

goals map_goals(proof_state const & s, std::function<optional<goal>(goal const & g)> f);

UDATA_DEFS_CORE(goals)
UDATA_DEFS(proof_state)
void open_proof_state(lua_State * L);

void initialize_proof_state();
void finalize_proof_state();
}
