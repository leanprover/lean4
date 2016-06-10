/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/lazy_abstraction.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj tactic_intro_core(name const & n, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception();
    metavar_context mctx = s.mctx();
    type_context ctx     = mk_type_context_for(s, mctx);
    expr type            = g->get_type();
    if (!is_pi(type) && !is_let(type)) {
        type             = ctx.whnf(type);
        if (!is_pi(type))
            return mk_tactic_exception("intro tactic failed, Pi/let expression expected");
    }
    local_context lctx   = g->get_context();
    if (is_pi(type)) {
        name n1              = n == "_" ? binding_name(type) : n;
        expr H               = lctx.mk_local_decl(n1, binding_domain(type), binding_info(type));
        expr new_type        = instantiate(binding_body(type), H);
        expr new_M           = mctx.mk_metavar_decl(lctx, new_type);
        expr new_val         = mk_lambda(n1, binding_domain(type), mk_lazy_abstraction(mlocal_name(H), new_M));
        mctx.assign(head(s.goals()), new_val);
        list<expr> new_gs(new_M, tail(s.goals()));
        return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
    } else {
        lean_assert(is_let(type));
        name n1              = n == "_" ? let_name(type) : n;
        expr H               = lctx.mk_local_decl(n1, let_type(type), let_value(type));
        expr new_type        = instantiate(let_body(type), H);
        expr new_M           = mctx.mk_metavar_decl(lctx, new_type);
        expr new_val         = mk_let(n1, let_type(type), let_value(type), mk_lazy_abstraction(mlocal_name(H), new_M));
        mctx.assign(head(s.goals()), new_val);
        list<expr> new_gs(new_M, tail(s.goals()));
        return mk_tactic_success(set_mctx_goals(s, mctx, new_gs));
    }
}

vm_obj tactic_intro(vm_obj const & n, vm_obj const & s) {
    return tactic_intro_core(to_name(n), to_tactic_state(s));
}

void initialize_intro_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "intro"}),   tactic_intro);
}

void finalize_intro_tactic() {
}
}
