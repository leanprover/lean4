/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/blast/hypothesis.h"
namespace lean {
namespace blast {
optional<expr> assumption_action();
/** \brief Apply assumption and contradiction actions using the given hypothesis.
    \remark This action is supposed to be applied when a hypothesis is activated. */
optional<expr> assumption_contradiction_actions(hypothesis_idx hidx);
/** \brief Solve trivial targets (e.g., true, a = a, a <-> a, etc). */
optional<expr> trivial_action();

/** \brief Return true if the given hypothesis is "redundant". We consider a hypothesis
    redundant if it is a proposition, no other hypothesis type depends on it,
    and one of the following holds:
    1- (H : true)
    2- (H : a ~ a)  where ~ is a reflexive relation
    3- There is another hypothesis H' with the same type.

    Remark: 2 is not needed if the simplification rule (a ~ a) <-> true is installed.

    Remark: we may want to generalize the proposition condition. Example: consider any subsingleton type.
    We don't do it because it seems to add extra cost for very little gain
    (well, it may be useful for the HoTT library).

    TODO(Leo): subsumption. 3 is just a very simple case of subsumption. */
bool discard(hypothesis_idx hidx);
}}
