/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "library/tactic/hsubstitution.h"

namespace lean {
typedef list<list<expr>>    intros_list;
typedef list<hsubstitution> hsubstitution_list;

/** \brief Apply the induction lemma \c rec_name on the hypothesis \c H at goal \c mvar.
    The tactic uses ns (if available) to name parameters associated with minor premises.

    If ilist != nullptr, then tactic stores the new hypotheses introduced for each new goal.
    If slist != nullptr, then tactic stores renamed hypotheses for each new goal.

    The result is a list of goals (new metavariables).

    \pre is_metavar(mvar)
    \pre is_local(H)
    \pre mctx.get_metavar_decl(mvar) != none

    \post ilist != nullptr ==> length(*ilist) == length(result)
    \post slist != nullptr ==> length(*slist) == length(result) */
list<expr> induction(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
                     expr const & mvar, expr const & H, name const & rec_name, list<name> & ns,
                     intros_list * ilist, hsubstitution_list * slist);

void initialize_induction_tactic();
void finalize_induction_tactic();
}
