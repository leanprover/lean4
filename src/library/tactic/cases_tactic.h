/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/induction_tactic.h"

namespace lean {
/** \brief Similar to induction, but applies 'cases_on' and has bettern support for dependent types. Failures are reported using exceptions.
    \c ids (if available) provides the names for new hypotheses.
    If ilist and rlist are not nullptr, then
    1- Store in ilist the new hypotheses introduced for each new goal.
    2- Store in rlist the hypotheses renamed in each new goal.
    \pre (ilist == nullptr) iff (rlist == nullptr)
    \post ilist != nullptr -> rlist != nullptr -> length(*ilist) == length(*rlist) */
list<expr> cases(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
                 expr const & mvar, expr const & H, list<name> & ids,
                 intros_list * ilist, renaming_list * rlist);
void initialize_cases_tactic();
void finalize_cases_tactic();
}
