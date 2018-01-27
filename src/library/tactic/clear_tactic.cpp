/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
expr clear(metavar_context & mctx, expr const & mvar, expr const & H) {
    lean_assert(is_metavar(mvar));
    lean_assert(is_local(H));
    optional<metavar_decl> g   = mctx.find_metavar_decl(mvar);
    if (!g) throw exception("clear tactic failed, there are no goals to be solved");
    local_context lctx         = g->get_context();
    optional<local_decl> d     = lctx.find_local_decl(H);
    if (!d)
        throw exception(sstream() << "clear tactic failed, unknown '" << mlocal_pp_name(H) << "' hypothesis");
    /* We don't need to traverse let-declarations because the lctx.has_dependencies(*d, mctx) will catch them. */
    if (depends_on(g->get_type(), mctx, 1, &H))
        throw exception(sstream() << "clear tactic failed, target type depends on '" << mlocal_pp_name(H) << "'");
    if (optional<local_decl> d2 = lctx.has_dependencies(*d, mctx))
        throw exception(sstream() << "clear tactic failed, hypothesis '" << d2->get_pp_name() << "' depends on '" << mlocal_pp_name(H) << "'");
    lctx.clear(*d);
    expr new_mvar              = mctx.mk_metavar_decl(lctx, g->get_type());
    mctx.assign(mvar, new_mvar);
    return new_mvar;
}

expr clear_rec_core(metavar_context & mctx, expr const & mvar) {
    optional<metavar_decl> g   = mctx.find_metavar_decl(mvar);
    lean_assert(g);
    local_context lctx         = g->get_context();
    if (optional<local_decl> d = lctx.find_if([](local_decl const & decl) { return decl.get_info().is_rec(); })) {
        return clear(mctx, mvar, d->mk_ref());
    } else {
        return mvar;
    }
}

expr clear_recs(metavar_context & mctx, expr const & mvar) {
    expr curr = mvar;
    while (true) {
        expr next = clear_rec_core(mctx, curr);
        if (next == curr)
            return curr;
        curr = next;
    }
}

vm_obj clear(expr const & H, tactic_state const & s) {
    lean_assert(is_local(H));
    try {
        optional<expr> mvar  = s.get_main_goal();
        if (!mvar) return mk_no_goals_exception(s);
        metavar_context mctx = s.mctx();
        expr new_mvar        = clear(mctx, *mvar, H);
        return tactic::mk_success(set_mctx_goals(s, mctx, cons(new_mvar, tail(s.goals()))));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj clear_internal(name const & n, tactic_state const & s) {
     optional<metavar_decl> g   = s.get_main_goal_decl();
     if (!g) return mk_no_goals_exception(s);
     metavar_context mctx       = s.mctx();
     local_context lctx         = g->get_context();
     optional<local_decl> d     = lctx.find_local_decl(n);
     if (!d)
         return tactic::mk_exception(sstream() << "clear tactic failed, unknown '" << n << "' hypothesis", s);
     return clear(d->mk_ref(), s);
}

vm_obj tactic_clear(vm_obj const & e0, vm_obj const & s) {
    expr const & e = to_expr(e0);
    if (!is_local(e))
        return tactic::mk_exception(sstream() << "clear tactic failed, given expression is not a local constant",
                                   tactic::to_state(s));
    return clear(e, tactic::to_state(s));
}

void initialize_clear_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "clear"}),    tactic_clear);
}

void finalize_clear_tactic() {
}
}
