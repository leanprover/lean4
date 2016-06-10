/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj assumption_core(tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception();
    metavar_context mctx       = s.mctx();
    type_context ctx           = mk_type_context_for(s, mctx, transparency_mode::Reducible);
    local_context const & lctx = g->get_context();
    expr const & type          = g->get_type();
    optional<local_decl> d = lctx.back_find_if([&](local_decl const & d) {
            return ctx.is_def_eq(type, d.get_type());
        });
    if (!d)
        return mk_tactic_exception("assumption tactic failed");
    mctx.assign(head(s.goals()), d->mk_ref());
    return mk_tactic_success(set_mctx_goals(s, mctx, tail(s.goals())));
}

vm_obj assumption(vm_obj const & s) {
    return assumption_core(to_tactic_state(s));
}

void initialize_assumption_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "assumption"}),   assumption);
}

void finalize_assumption_tactic() {
}
}
