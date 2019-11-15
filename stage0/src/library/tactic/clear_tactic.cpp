/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"

namespace lean {
expr clear(metavar_context & mctx, expr const & mvar, expr const & H) {
    lean_assert(is_metavar(mvar));
    lean_assert(is_fvar(H));
    optional<metavar_decl> g   = mctx.find_metavar_decl(mvar);
    if (!g) throw exception("clear tactic failed, there are no goals to be solved");
    local_context lctx         = g->get_context();
    optional<local_decl> d     = lctx.find_local_decl(H);
    if (!d)
        throw exception(sstream() << "clear tactic failed, unknown hypothesis");
    /* We don't need to traverse let-declarations because the lctx.has_dependencies(*d, mctx) will catch them. */
    if (depends_on(g->get_type(), mctx, 1, &H))
        throw exception(sstream() << "clear tactic failed, target type depends on '" << lctx.get_local_decl(H).get_user_name() << "'");
    if (optional<local_decl> d2 = lctx.has_dependencies(*d, mctx))
        throw exception(sstream() << "clear tactic failed, hypothesis '" << d2->get_user_name() << "' depends on '" << lctx.get_local_decl(H).get_user_name() << "'");
    lctx.clear(*d);
    expr new_mvar              = mctx.mk_metavar_decl(lctx, g->get_type());
    mctx.assign(mvar, new_mvar);
    return new_mvar;
}

void initialize_clear_tactic() {
}

void finalize_clear_tactic() {
}
}
