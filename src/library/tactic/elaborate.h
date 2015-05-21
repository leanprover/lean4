/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
bool solve_constraints(environment const & env, io_state const & ios, proof_state & ps, constraint_seq const & cs);

/** \brief Function for elaborating expressions nested in tactics.
    Some tactics contain nested expression (aka pre-terms) that need to be elaborated.
    The arguments are:
    1- goal that will provide the context where the expression will be elaborated
    2- name generator
    3- expression to be elaborated
    4- expected type
    5- substitution associated with the proof state
    6- a flag indicating whether the elaborator should report unassigned/unsolved placeholders
    The results are
    1- elaborated expression
    2- updated substitution
    3- postponed constraints
*/
typedef std::tuple<expr, substitution, constraints> elaborate_result;
typedef std::function<elaborate_result(goal const &, name_generator &&, expr const &,
                                       optional<expr> const &, substitution const &, bool)> elaborate_fn;

/** \brief Try to elaborate expression \c e using the elaboration function \c elab. The elaboration is performed
    with respect to (local context of) the first goal in \c s. The constraints generated during elaboration
    are solved using the higher-order unifier. When solving the constraints any postponed constraint in \c s
    is also considered. Only the first solution returned by the unifier is considered.
    If the whole process succeeds, then the elaborated expression is returned, and the proof state is updated.
    The following fields in the name generator may be updated: name-generator and substitution.

    If the proof state has no goal, the elaboration or unifier fails, then none is returned and the proof state
    is not modified.
*/
optional<expr> elaborate_with_respect_to(environment const & env, io_state const & ios, elaborate_fn const & elab,
                                         proof_state & s, expr const & e,
                                         optional<expr> const & expected_type = optional<expr>(),
                                         bool report_unassigned = false, bool enforce_type_during_elaboration = false);
}
