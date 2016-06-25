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
vm_obj assert_define(bool is_assert, name const & n, expr const & t, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx     = mk_type_context_for(s);
    if (!is_sort(ctx.whnf(ctx.infer(t)))) {
        format msg("invalid ");
        if (is_assert) msg += format("assert"); else msg += format("define");
        msg += format(" tactic, expression is not a type");
        msg += pp_indented_expr(s, t);
        return mk_tactic_exception(msg, s);
    }
    local_context lctx   = g->get_context();
    metavar_context mctx = ctx.mctx();
    expr new_M_1         = mctx.mk_metavar_decl(lctx, t);
    expr l;
    if (is_assert)
        l = lctx.mk_local_decl(n, t);
    else
        l = lctx.mk_local_decl(n, t, new_M_1);
    expr new_M_2         = mctx.mk_metavar_decl(lctx, g->get_type());
    expr new_val;
    if (is_assert)
        new_val = mk_app(mk_lambda(n, t, mk_lazy_abstraction(new_M_2, mlocal_name(l))), new_M_1);
    else
        new_val = mk_let(n, t, new_M_1, mk_lazy_abstraction(new_M_2, mlocal_name(l)));
    mctx.assign(head(s.goals()), new_val);
    list<expr> new_gs    = cons(new_M_1, cons(new_M_2, tail(s.goals())));
    return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
}

vm_obj tactic_assert(vm_obj const & n, vm_obj const & t, vm_obj const & s) {
    return assert_define(true, to_name(n), to_expr(t), to_tactic_state(s));
}

vm_obj tactic_define(vm_obj const & n, vm_obj const & t, vm_obj const & s) {
    return assert_define(false, to_name(n), to_expr(t), to_tactic_state(s));
}

vm_obj assertv_definev(bool is_assert, name const & n, expr const & t, expr const & v, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx     = mk_type_context_for(s);
    expr v_type          = ctx.infer(v);
    if (!ctx.is_def_eq(t, v_type)) {
        format msg("invalid ");
        if (is_assert) msg += format("assertv"); else msg += format("definev");
        msg += format(" tactic, value has type");
        msg += pp_indented_expr(s, v_type);
        msg += line() + format("but is expected to have type");
        msg += pp_indented_expr(s, t);
        return mk_tactic_exception(msg, s);
    }
    local_context lctx   = g->get_context();
    metavar_context mctx = ctx.mctx();
    expr l;
    if (is_assert)
        l = lctx.mk_local_decl(n, t);
    else
        l = lctx.mk_local_decl(n, t, v);
    expr new_M           = mctx.mk_metavar_decl(lctx, g->get_type());
    expr new_val;
    if (is_assert)
        new_val = mk_app(mk_lambda(n, t, mk_lazy_abstraction(new_M, mlocal_name(l))), v);
    else
        new_val = mk_let(n, t, v, mk_lazy_abstraction(new_M, mlocal_name(l)));
    mctx.assign(head(s.goals()), new_val);
    list<expr> new_gs    = cons(new_M, tail(s.goals()));
    return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
}

vm_obj tactic_assertv(vm_obj const & n, vm_obj const & e, vm_obj const & pr, vm_obj const & s) {
    return assertv_definev(true, to_name(n), to_expr(e), to_expr(pr), to_tactic_state(s));
}

vm_obj tactic_definev(vm_obj const & n, vm_obj const & e, vm_obj const & pr, vm_obj const & s) {
    return assertv_definev(false, to_name(n), to_expr(e), to_expr(pr), to_tactic_state(s));
}

void initialize_assert_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "assert"}),  tactic_assert);
    DECLARE_VM_BUILTIN(name({"tactic", "assertv"}), tactic_assertv);
    DECLARE_VM_BUILTIN(name({"tactic", "define"}),  tactic_define);
    DECLARE_VM_BUILTIN(name({"tactic", "definev"}), tactic_definev);
}

void finalize_assert_tactic() {
}
}
