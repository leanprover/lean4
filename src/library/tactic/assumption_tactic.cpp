/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"

namespace lean {
optional<tactic_state> assumption(tactic_state const & s) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    lean_assert(g);
    metavar_context mctx       = s.mctx();
    type_context ctx           = mk_type_context_for(s, mctx, transparency_mode::Reducible);
    local_context const & lctx = g->get_context();
    expr const & type          = g->get_type();
    optional<local_decl> d = lctx.back_find_if([&](local_decl const & d) {
            return ctx.is_def_eq(type, d.get_type());
        });
    if (!d) return none_tactic_state();
    mctx.assign(head(s.goals()), d->mk_ref());
    return some_tactic_state(set_mctx_goals(s, mctx, tail(s.goals())));
}

vm_obj tactic_assumption(vm_obj const & s) {
    optional<metavar_decl> g = to_tactic_state(s).get_main_goal_decl();
    if (!g) return mk_no_goals_exception(to_tactic_state(s));
    if (auto r = assumption(to_tactic_state(s)))
        return mk_tactic_success(*r);
    else
        return mk_tactic_exception("assumption tactic failed", to_tactic_state(s));
}

void initialize_assumption_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "assumption"}), tactic_assumption);
}

void finalize_assumption_tactic() {
}
}
