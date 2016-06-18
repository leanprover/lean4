/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj clear(name const & n, tactic_state const & s, bool internal_name) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx       = s.mctx();
    local_context lctx         = g->get_context();
    optional<local_decl> d     = internal_name ? lctx.get_local_decl(n) : lctx.get_local_decl_from_user_name(n);
    if (!d)
        return mk_tactic_exception(sstream() << "clear tactic failed, unknown '" << n << "' hypothesis", s);
    expr l = d->mk_ref();
    if (depends_on(g->get_type(), 1, &l))
        return mk_tactic_exception(sstream() << "clear tactic failed, result type depends on '" << n << "'", s);
    if (optional<local_decl> d2 = lctx.has_dependencies(*d))
        return mk_tactic_exception(sstream() << "clear tactic failed, '" << d2->get_pp_name() << "' depends on '"
                                   << n << "'", s);
    lctx.clear(*d);
    expr new_g                 = mctx.mk_metavar_decl(lctx, g->get_type());
    mctx.assign(head(s.goals()), new_g);
    return mk_tactic_success(set_mctx_goals(s, mctx, cons(new_g, tail(s.goals()))));
}

vm_obj tactic_clear(vm_obj const & n, vm_obj const & s) {
    bool internal_name = false;
    return clear(to_name(n), to_tactic_state(s), internal_name);
}

vm_obj tactic_clear_fv(vm_obj const & e0, vm_obj const & s) {
    expr const & e = to_expr(e0);
    if (!is_local(e))
        return mk_tactic_exception(sstream() << "clear_fv tactic failed, given expression is not a free-variable",
                                   to_tactic_state(s));
    return clear(mlocal_name(e), to_tactic_state(s), true);
}

void initialize_clear_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "clear"}),    tactic_clear);
    DECLARE_VM_BUILTIN(name({"tactic", "clear_fv"}), tactic_clear_fv);
}

void finalize_clear_tactic() {
}
}
