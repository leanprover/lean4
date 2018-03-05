/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/delayed_abstraction.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"

namespace lean {
vm_obj assert_define_core(bool is_assert, name const & n, expr const & t, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context_old ctx     = mk_type_context_for(s);
    if (!is_sort(ctx.whnf(ctx.infer(t)))) {
        format msg("invalid ");
        if (is_assert) msg += format("assert"); else msg += format("define");
        msg += format(" tactic, expression is not a type");
        msg += pp_indented_expr(s, t);
        return tactic::mk_exception(msg, s);
    }
    local_context lctx   = g->get_context();
    expr new_M_1         = ctx.mk_metavar_decl(lctx, t);
    expr new_M_2, new_val;
    if (is_assert) {
        expr new_target  = mk_pi(n, t, g->get_type());
        new_M_2          = ctx.mk_metavar_decl(lctx, new_target);
        new_val          = mk_app(new_M_2, new_M_1);
    } else {
        expr new_target  = mk_let(n, t, new_M_1, g->get_type());
        new_M_2          = ctx.mk_metavar_decl(lctx, new_target);
        new_val          = new_M_2;
    }
    ctx.assign(head(s.goals()), new_val);
    list<expr> new_gs    = cons(new_M_1, cons(new_M_2, tail(s.goals())));
    return tactic::mk_success(set_mctx_goals(s, ctx.mctx(), new_gs));
}

vm_obj tactic_assert_core(vm_obj const & n, vm_obj const & t, vm_obj const & s) {
    return assert_define_core(true, to_name(n), to_expr(t), tactic::to_state(s));
}

vm_obj tactic_define_core(vm_obj const & n, vm_obj const & t, vm_obj const & s) {
    return assert_define_core(false, to_name(n), to_expr(t), tactic::to_state(s));
}

vm_obj assertv_definev_core(bool is_assert, name const & n, expr const & t, expr const & v, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context_old ctx     = mk_type_context_for(s);
    expr v_type          = ctx.infer(v);
    if (!ctx.is_def_eq(t, v_type)) {
        auto thunk = [=]() {
            format msg("invalid ");
            if (is_assert) msg += format("assertv"); else msg += format("definev");
            msg += format(" tactic, value has type");
            msg += pp_indented_expr(s, v_type);
            msg += line() + format("but is expected to have type");
            msg += pp_indented_expr(s, t);
            return msg;
        };
        return tactic::mk_exception(thunk, s);
    }
    local_context lctx   = g->get_context();
    expr new_M, new_val;
    if (is_assert) {
        expr new_target  = mk_pi(n, t, g->get_type());
        new_M            = ctx.mk_metavar_decl(lctx, new_target);
        new_val          = mk_app(new_M, v);
    } else {
        expr new_target  = mk_let(n, t, v, g->get_type());
        new_M            = ctx.mk_metavar_decl(lctx, new_target);
        new_val          = new_M;
    }
    ctx.assign(head(s.goals()), new_val);
    list<expr> new_gs    = cons(new_M, tail(s.goals()));
    return tactic::mk_success(set_mctx_goals(s, ctx.mctx(), new_gs));
}

vm_obj tactic_assertv_core(vm_obj const & n, vm_obj const & e, vm_obj const & pr, vm_obj const & s) {
    return assertv_definev_core(true, to_name(n), to_expr(e), to_expr(pr), tactic::to_state(s));
}

vm_obj tactic_definev_core(vm_obj const & n, vm_obj const & e, vm_obj const & pr, vm_obj const & s) {
    return assertv_definev_core(false, to_name(n), to_expr(e), to_expr(pr), tactic::to_state(s));
}

vm_obj assertv_definev(bool is_assert, name const & n, expr const & t, expr const & v, tactic_state const & s) {
    vm_obj r = assertv_definev_core(is_assert, n, t, v, s);
    if (optional<tactic_state> const & s2 = tactic::is_success(r)) {
        return intro(n, *s2);
    } else {
        return r;
    }
}

void initialize_assert_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "assert_core"}),  tactic_assert_core);
    DECLARE_VM_BUILTIN(name({"tactic", "assertv_core"}), tactic_assertv_core);
    DECLARE_VM_BUILTIN(name({"tactic", "define_core"}),  tactic_define_core);
    DECLARE_VM_BUILTIN(name({"tactic", "definev_core"}), tactic_definev_core);
}

void finalize_assert_tactic() {
}
}
