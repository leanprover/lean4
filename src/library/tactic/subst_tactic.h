/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "library/tactic/hsubstitution.h"

namespace lean {
/** \brief Given (H : lhs = rhs), replace lhs with rhs in the goal \c mvar. If symm == true, then replace rhs with lhs.
    The replaced term must be a local constant. If substs is not nullptr, then hypotheses renamed by revert/intro
    are stored in \c substs, and the actual substitution.

    \pre is_metavar(mvar)
    \pre is_local(H)
    \pre mctx.get_metavar_decl(mvar) != none
    \pre typeof(H) is an equality
    \pre symm == false ==> is_local(lhs(typeof(H)))
    \pre symm == true  ==> is_local(rhs(typeof(H))) */
expr subst(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
           expr const & mvar, expr const & H, bool symm, hsubstitution * substs);

vm_obj tactic_subst(expr const & l, tactic_state const & s);

void initialize_subst_tactic();
void finalize_subst_tactic();
}
