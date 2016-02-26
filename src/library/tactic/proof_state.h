/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <algorithm>
#include <functional>
#include "util/optional.h"
#include "util/name_set.h"
#include "kernel/metavar.h"
#include "library/tactic/goal.h"

namespace lean {
typedef list<goal> goals;
class proof_state {
    goals            m_goals;
    substitution     m_subst;
    constraints      m_postponed;
    bool             m_report_failure;

    format pp_core(std::function<formatter()> const & mk_fmt, options const & opts) const;

public:
    proof_state(goals const & gs, substitution const & s, constraints const & postponed,
                bool report_failure = true);
    proof_state(proof_state const & s, goals const & gs, substitution const & subst,
                constraints const & postponed):
        proof_state(gs, subst, postponed, s.report_failure()) {}
    proof_state(proof_state const & s, goals const & gs, substitution const & subst):
        proof_state(gs, subst, s.m_postponed, s.report_failure()) {}
    proof_state(proof_state const & s, goals const & gs):
        proof_state(s, gs, s.m_subst) {}
    proof_state(proof_state const & s, substitution const & subst,
                constraints const & postponed):
        proof_state(s.m_goals, subst, postponed, s.report_failure()) {}
    proof_state(proof_state const & s, constraints const & postponed):
        proof_state(s, s.m_goals, s.m_subst, postponed) {}
    proof_state(proof_state const & s, substitution const & subst):
        proof_state(s, s.m_goals, subst, s.m_postponed) {}
    proof_state(proof_state const & s):
        proof_state(s, s.m_postponed) {}

    proof_state update_report_failure(bool f) const {
        return m_report_failure == f ? *this : proof_state(m_goals, m_subst, m_postponed, f);
    }

    goals const & get_goals() const { return m_goals; }
    substitution const & get_subst() const { return m_subst; }
    constraints const & get_postponed() const { return m_postponed; }
    bool report_failure() const { return m_report_failure; }

    /** \brief Return true iff this state does not have any goals left */
    bool is_final_state() const { return empty(m_goals); }

    format pp(formatter const & fmt) const;
};

/** \brief Apply substitution stored in \c s to main goal */
proof_state apply_substitution(proof_state const & s);

inline optional<proof_state> some_proof_state(proof_state const & s) { return some(s); }
inline optional<proof_state> none_proof_state() { return optional<proof_state> (); }

proof_state to_proof_state(expr const & meta, expr const & type, substitution const & subst);
proof_state to_proof_state(expr const & meta, expr const & type);

goals map_goals(proof_state const & s, std::function<optional<goal>(goal const & g)> f);

void initialize_proof_state();
void finalize_proof_state();
}
