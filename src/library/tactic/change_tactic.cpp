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
vm_obj change_core(expr const & e, bool check, tactic_state const & s) {
    try {
        optional<metavar_decl> g = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        if (e == g->get_type()) return tactic::mk_success(s);
        type_context_old ctx         = mk_type_context_for(s);
        if (!check || ctx.is_def_eq(e, g->get_type())) {
            expr new_e   = ctx.instantiate_mvars(e);
            expr new_M   = ctx.mk_metavar_decl(g->get_context(), new_e);
            /*
               We use the proof term

                  (@id (g->get_type()) new_M)

               to create a "checkpoint". See discussion at issue #1260
            */
            expr  pr  = mk_id(ctx, g->get_type(), new_M);
            auto mctx    = ctx.mctx();
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
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj change(expr const & e, tactic_state const & s) {
    return change_core(e, true, s);
}

vm_obj tactic_change(vm_obj const & e, vm_obj const & check, vm_obj const & s) {
    return change_core(to_expr(e), to_bool(check), tactic::to_state(s));
}

void initialize_change_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "change"}),   tactic_change);
}

void finalize_change_tactic() {
}
}
