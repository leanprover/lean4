/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj change(expr const & e, tactic_state const & s) {
    try {
        optional<metavar_decl> g = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        metavar_context mctx     = s.mctx();
        type_context ctx         = mk_type_context_for(s, mctx);
        if (ctx.is_def_eq(e, g->get_type())) {
            expr new_M   = mctx.mk_metavar_decl(g->get_context(), e);
            mctx.assign(head(s.goals()), new_M);
            list<expr> new_gs(new_M, tail(s.goals()));
            return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
        } else {
            format m("tactic.change failed, given type");
            m += pp_indented_expr(s, e);
            m += format("is not definitionally equal to");
            m += pp_indented_expr(s, g->get_type());
            return mk_tactic_exception(m, s);
        }
    } catch (exception & e) {
        return mk_tactic_exception(e, s);
    }
}

vm_obj tactic_change(vm_obj const & e, vm_obj const & s) {
    return change(to_expr(e), to_tactic_state(s));
}

void initialize_change_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "change"}),   tactic_change);
}

void finalize_change_tactic() {
}
}
