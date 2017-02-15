/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/app_builder_tactics.h"

namespace lean {

vm_obj exact(expr const & e, transparency_mode const & m, tactic_state const & s) {
    try {
        optional<metavar_decl> g = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        type_context ctx     = mk_type_context_for(s, m);
        expr e_type          = ctx.infer(e);
        if (!ctx.is_def_eq(g->get_type(), e_type)) {
            auto thunk = [=]() {
                format r("exact tactic failed, type mismatch, given expression has type");
                unsigned indent = get_pp_indent(s.get_options());
                r += nest(indent, line() + pp_expr(s, e_type));
                r += line() + format("but is expected to have type");
                r += nest(indent, line() + pp_expr(s, g->get_type()));
                return r;
            };
            return mk_tactic_exception(thunk, s);
        }
        auto mctx = ctx.mctx();
        mctx.assign(head(s.goals()), e);
        return mk_tactic_success(set_mctx_goals(s, mctx, tail(s.goals())));
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_exact(vm_obj const & e, vm_obj const & m, vm_obj const & s) {
    return exact(to_expr(e), to_transparency_mode(m), to_tactic_state(s));
}

void initialize_exact_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "exact"}), tactic_exact);
}

void finalize_exact_tactic() {
}
}
