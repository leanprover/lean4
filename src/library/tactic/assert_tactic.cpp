/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/lazy_abstraction.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj assert_core(name const & n, expr const & e, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx = s.mctx();
    type_context ctx     = mk_type_context_for(s, mctx);
    if (!is_sort(ctx.whnf(ctx.infer(e)))) {
        format msg("invalid assert tactic, expression is not a type");
        msg += pp_indented_expr(s, e);
        return mk_tactic_exception(msg, s);
    }
    local_context lctx   = g->get_context();
    expr new_M_1         = mctx.mk_metavar_decl(lctx, e);
    expr l               = lctx.mk_local_decl(n, e, new_M_1);
    expr new_M_2         = mctx.mk_metavar_decl(lctx, g->get_type());
    expr new_val         = mk_let(n, e, new_M_1, mk_lazy_abstraction(new_M_2, mlocal_name(l)));
    mctx.assign(head(s.goals()), new_val);
    list<expr> new_gs    = cons(new_M_1, cons(new_M_2, tail(s.goals())));
    return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
}

vm_obj tactic_assert(vm_obj const & n, vm_obj const & e, vm_obj const & s) {
    return assert_core(to_name(n), to_expr(e), to_tactic_state(s));
}

vm_obj pose(name const & n, expr const & e, expr const & pr, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx = s.mctx();
    type_context ctx     = mk_type_context_for(s, mctx);
    expr pr_type         = ctx.infer(pr);
    if (!ctx.is_def_eq(e, pr_type)) {
        format msg("invalid pose tactic, proof has type");
        msg += pp_indented_expr(s, pr_type);
        msg += line() + format("but is expected to have type");
        msg += pp_indented_expr(s, e);
        return mk_tactic_exception(msg, s);
    }
    local_context lctx   = g->get_context();
    expr l               = lctx.mk_local_decl(n, e);
    expr new_M           = mctx.mk_metavar_decl(lctx, g->get_type());
    expr new_val         = mk_app(mk_lambda(n, e, mk_lazy_abstraction(new_M, mlocal_name(l))), pr);
    mctx.assign(head(s.goals()), new_val);
    list<expr> new_gs    = cons(new_M, tail(s.goals()));
    return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
}

vm_obj tactic_pose(vm_obj const & n, vm_obj const & e, vm_obj const & pr, vm_obj const & s) {
    return pose(to_name(n), to_expr(e), to_expr(pr), to_tactic_state(s));
}

void initialize_assert_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "assert"}), tactic_assert);
    DECLARE_VM_BUILTIN(name({"tactic", "pose"}),   tactic_pose);
}

void finalize_assert_tactic() {
}
}
