/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
namespace lean {
optional<tactic_state> intron(unsigned n, tactic_state const & s, buffer<name> & new_Hs, bool use_unused_names);
optional<tactic_state> intron(unsigned n, tactic_state const & s, bool use_unused_names);
/* Low-level versions of the previous procedures, they allow us to intron in any goal.
   The new hypotheses "user names" are generated using \c new_hs_names (when available).
   After execution, the buffer \c new_Hns stores the new interal names for the new hypotheses.

   \remark new_hs_names is an input/output parameter. The procedure will "consume" n elements from the list.

   \remark if new_hs_names doesn't have sufficient names, then the procedure
   will create unused local context names using the binder names. */
optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, list<name> & new_hs_names, buffer<name> & new_Hns,
                      bool use_unused_names);
optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, list<name> & new_hs_names,
                      bool use_unused_names);
optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, buffer<name> & new_Hns,
                      bool use_unused_names);
optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, bool use_unused_names);

/* Low-level version of `intron` where a procedure for generating names is provided by the user.
   The argument `n` in `mk_name` is the name in the binder (i.e., Pi/let-expr). */
optional<expr> intron_core(environment const & env, options const & opts, metavar_context & mctx,
                           expr const & mvar, unsigned n, buffer<name> & new_Hns,
                           std::function<name(local_context const & lctx, name const & n)> const & mk_name);

vm_obj intro(name const & n, tactic_state const & s);

void initialize_intro_tactic();
void finalize_intro_tactic();
}
