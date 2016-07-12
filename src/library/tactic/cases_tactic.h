/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"

namespace lean {
typedef list<list<name>>     intros_list;
typedef list<name_map<name>> renaming_list;

/** \brief Apply cases tactic to H. Failures are reported using exceptions.
    \c ids (if available) provides the names for new hypotheses.
    If ilist and rlist are not nullptr, then
    1- Store in ilist the new hypotheses introduced for each new goal.
    2- Store in rlist the hypotheses renamed in each new goal.
    \pre (ilist == nullptr) iff (rlist == nullptr)
    \post ilist != nullptr -> rlist != nullptr -> length(*ilist) == length(*rlist) */
tactic_state cases(tactic_state const & s, transparency_mode m, expr const & H, list<name> const & ids, intros_list * ilist, renaming_list * rlist);
void initialize_cases_tactic();
void finalize_cases_tactic();
}
