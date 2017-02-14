/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/kabstract.h"

namespace lean {
vm_obj generalize(transparency_mode m, expr const & e, name const & id, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx = mk_type_context_for(s, m);
    expr target = ctx.instantiate_mvars(g->get_type());
    expr target_abst = kabstract(ctx, target, e);
    if (closed(target_abst))
        return mk_tactic_exception("generalize tactic failed, failed to find expression in the target", s);
    expr e_type   = ctx.infer(e);
    expr new_type = mk_pi(id, e_type, target_abst);
    metavar_context mctx = ctx.mctx();
    expr mvar     = mctx.mk_metavar_decl(g->get_context(), new_type);
    mctx.assign(head(s.goals()), mk_app(mvar, e));
    return mk_tactic_success(set_mctx_goals(s, mctx, cons(mvar, tail(s.goals()))));
}

vm_obj tactic_generalize(vm_obj const & e, vm_obj const & n, vm_obj const & m, vm_obj const & s) {
    return generalize(to_transparency_mode(m), to_expr(e), to_name(n), to_tactic_state(s));
}

void initialize_generalize_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "generalize"}),   tactic_generalize);
}

void finalize_generalize_tactic() {
}
}
