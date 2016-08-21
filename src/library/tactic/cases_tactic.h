/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/induction_tactic.h"

namespace lean {
typedef list<list<optional<name>>>  cintros_list;

/** \brief Similar to induction, but applies 'cases_on' and has bettern support for dependent types. Failures are reported using exceptions.
    \c ids (if available) provides the names for new hypotheses.
    If cilist and rlist are not nullptr, then
    1- Store in ilist the new hypotheses introduced for each new goal.
       We have a new hypothesis for each constructor field.
       The entry is none if the field was eliminated during dependent pattern matching.
    2- Store in rlist the hypotheses renamed in each new goal.
    \pre (ilist == nullptr) iff (rlist == nullptr)
    \post ilist != nullptr -> rlist != nullptr -> length(*ilist) == length(*rlist)

    The result is a new list of goals and a list of constructor names.
    The two lists have the same size. Let (m, c) be the i-th elements of each list.
    Then we have that m is the goal associated with the constructor c.

    \remark The resulting set of goals may be smaller than the number of constructors
    since some of the goals are discarded. */
pair<list<expr>, list<name>>
cases(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
      expr const & mvar, expr const & H, list<name> & ids, cintros_list * ilist, renaming_list * rlist);

void initialize_cases_tactic();
void finalize_cases_tactic();
}
