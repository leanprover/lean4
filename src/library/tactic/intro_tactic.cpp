/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj tactic_intro_core(name const & n, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal();
    if (!g) return mk_no_goals_exception();
    metavar_context mctx = s.mctx();
    type_context ctx     = mk_type_context_for(s, mctx);
    expr type            = ctx.whnf(g->get_type());
    if (!is_pi(type))
        return mk_tactic_exception("intro tactic failed, Pi type expected");
    local_context lctx   = g->get_context();
    expr H               = lctx.mk_local_decl(binding_name(type), binding_domain(type), binding_info(type));
    expr new_type        = instantiate(binding_body(type), H);
    expr new_M           = mctx.mk_metavar_decl(lctx, new_type);
    // TODO(Leo)
    lean_unreachable();
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
