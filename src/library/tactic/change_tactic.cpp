/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj change(expr const & e, tactic_state const & s) {
    try {
        optional<metavar_decl> g = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        if (e == g->get_type()) return tactic::mk_success(s);
        type_context ctx         = mk_type_context_for(s);
        if (ctx.is_def_eq(e, g->get_type())) {
            auto mctx    = ctx.mctx();
            expr new_M   = mctx.mk_metavar_decl(g->get_context(), e);
            /*
               We use the proof term

                  (@id_locked (g->get_type()) new_M)

               to create a "checkpoint". See discussion at issue #1260
            */
            expr  pr  = mk_id_locked(ctx, g->get_type(), new_M);
            mctx.assign(head(s.goals()), pr);
            list<expr> new_gs(new_M, tail(s.goals()));
            return tactic::mk_success(set_mctx_goals(s, mctx, new_gs));
        } else {
            auto thunk = [=]() {
                format m("tactic.change failed, given type");
                m += pp_indented_expr(s, e);
                m += line() + format("is not definitionally equal to");
                m += pp_indented_expr(s, g->get_type());
                return m;
            };
            return tactic::mk_exception(thunk, s);
        }
    } catch (exception & e) {
        return tactic::mk_exception(e, s);
    }
}

vm_obj tactic_change(vm_obj const & e, vm_obj const & s) {
    return change(to_expr(e), tactic::to_state(s));
}

void initialize_change_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "change"}),   tactic_change);
}

void finalize_change_tactic() {
}
}
