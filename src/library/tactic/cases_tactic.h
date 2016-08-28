/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/induction_tactic.h"

namespace lean {
typedef list<list<expr>>    xintros_list;
typedef name_map<expr>      substitutions;
typedef list<substitutions> substitutions_list;

/* \brief Given `e`, for each (x := v) in `s` replace `x` with `v` in `e` */
expr apply_substitutions(expr const & e, substitutions const & s);
list<expr> apply_substitutions(list<expr> const & es, substitutions const & s);

/* \brief Return a new set of substitutions containing (x := apply_substitutions(v, s2)) for
   each (x := v) in `s1`. */
substitutions apply_substitutions(substitutions const & s1, substitutions const & s2);

/* \brief Return a new set of substitutions containing the entries of `s1` and `s2`. */
substitutions merge(substitutions const & s1, substitutions const & s2);

/** \brief Similar to induction, but applies 'cases_on' and has bettern support for dependent types. Failures are reported using exceptions.
    \c ids (if available) provides the names for new hypotheses.
    If ilist and slist are not nullptr, then
    1- Store in ilist the new "hypotheses" introduced for each new goal.
       We have a new "hypothesis" for each constructor field.
       We say "hypothesis" because it may be an arbitrary term.
       This may happen because of dependent pattern matching.
    2- Store in slist the hypotheses that have been replaced in each goal.

    \pre (ilist == nullptr) iff (slist == nullptr)
    \post ilist != nullptr -> slist != nullptr -> length(*ilist) == length(*slist)

    The result is a new list of goals and a list of constructor names.
    The two lists have the same size. Let (m, c) be the i-th elements of each list.
    Then we have that m is the goal associated with the constructor c.

    \remark The resulting set of goals may be smaller than the number of constructors
    since some of the goals are discarded. */
pair<list<expr>, list<name>>
cases(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
      expr const & mvar, expr const & H, list<name> & ids, xintros_list * ilist, substitutions_list * slist);

void initialize_cases_tactic();
void finalize_cases_tactic();
}
