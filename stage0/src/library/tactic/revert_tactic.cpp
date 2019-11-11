/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/tactic/tactic_state.h"

namespace lean {
expr revert(environment const & env, options const & opts, metavar_context & mctx, expr const & mvar, buffer<expr> & locals,
            bool preserve_locals_order) {
    optional<metavar_decl> g   = mctx.find_metavar_decl(mvar);
    lean_assert(g);
    type_context_old ctx           = mk_type_context_for(env, opts, mctx, g->get_context(), transparency_mode::All);
    expr val                   = ctx.revert(locals, mvar, preserve_locals_order);
    expr new_g                 = get_app_fn(val);
    mctx                       = ctx.mctx();
    return new_g;
}

tactic_state revert(buffer<expr> & locals, tactic_state const & s, bool preserve_locals_order) {
    lean_assert(s.goals());
    metavar_context mctx = s.mctx();
    expr new_g = revert(s.env(), s.get_options(), mctx, head(s.goals()), locals, preserve_locals_order);
    return set_mctx_goals(s, mctx, cons(new_g, tail(s.goals())));
}

void initialize_revert_tactic() {
}

void finalize_revert_tactic() {
}
}
