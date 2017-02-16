/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj rename(name const & from, name const & to, tactic_state const & s) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    metavar_context mctx       = s.mctx();
    local_context lctx         = g->get_context();
    if (!lctx.rename_user_name(from, to)) {
        return tactic::mk_exception(sstream() << "rename tactic failed, unknown '" << from << "' hypothesis", s);
    }
    expr new_g                 = mctx.mk_metavar_decl(lctx, g->get_type());
    mctx.assign(head(s.goals()), new_g);
    return tactic::mk_success(set_mctx_goals(s, mctx, cons(new_g, tail(s.goals()))));
}

vm_obj tactic_rename(vm_obj const & from, vm_obj const & to, vm_obj const & s) {
    return rename(to_name(from), to_name(to), tactic::to_state(s));
}

void initialize_rename_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "rename"}), tactic_rename);
}

void finalize_rename_tactic() {
}
}
