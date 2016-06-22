/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj clear(expr const & l, tactic_state const & s) {
    lean_assert(is_local(l));
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx       = s.mctx();
    local_context lctx         = g->get_context();
    optional<local_decl> d     = lctx.get_local_decl(l);
    if (!d)
        return mk_tactic_exception(sstream() << "clear tactic failed, unknown '" << local_pp_name(l) << "' hypothesis", s);
    if (depends_on(g->get_type(), 1, &l))
        return mk_tactic_exception(sstream() << "clear tactic failed, result type depends on '" << local_pp_name(l) << "'", s);
    if (optional<local_decl> d2 = lctx.has_dependencies(*d))
        return mk_tactic_exception(sstream() << "clear tactic failed, '" << d2->get_pp_name() << "' depends on '"
                                   << local_pp_name(l) << "'", s);
    lctx.clear(*d);
    expr new_g                 = mctx.mk_metavar_decl(lctx, g->get_type());
    mctx.assign(head(s.goals()), new_g);
    return mk_tactic_success(set_mctx_goals(s, mctx, cons(new_g, tail(s.goals()))));
}

vm_obj clear_internal(name const & n, tactic_state const & s) {
     optional<metavar_decl> g   = s.get_main_goal_decl();
     if (!g) return mk_no_goals_exception(s);
     metavar_context mctx       = s.mctx();
     local_context lctx         = g->get_context();
     optional<local_decl> d     = lctx.get_local_decl(n);
     if (!d)
         return mk_tactic_exception(sstream() << "clear tactic failed, unknown '" << n << "' hypothesis", s);
     return clear(d->mk_ref(), s);
}

vm_obj tactic_clear(vm_obj const & e0, vm_obj const & s) {
    expr const & e = to_expr(e0);
    if (!is_local(e))
        return mk_tactic_exception(sstream() << "clear tactic failed, given expression is not a local constant",
                                   to_tactic_state(s));
    return clear(e, to_tactic_state(s));
}

void initialize_clear_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "clear"}),    tactic_clear);
}

void finalize_clear_tactic() {
}
}
