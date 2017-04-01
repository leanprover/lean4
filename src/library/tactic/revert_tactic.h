/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
/** \brief revert the given hypothesis in the main goal.
    Update \c hs with the set of hypothesis that have been reverted (dependencies are reverted too).
    The final content of \c hs is a superset of the initial one. */
tactic_state revert(buffer<expr> & hs, tactic_state const & s, bool preserve_hs_order);

/* Low level version of revert tactic */
expr revert(environment const & env, options const & opts, metavar_context & mctx, expr const & mvar, buffer<expr> & locals,
            bool preserve_locals_order);

void initialize_revert_tactic();
void finalize_revert_tactic();
}
