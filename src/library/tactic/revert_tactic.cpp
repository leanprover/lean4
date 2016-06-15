/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"

namespace lean {
tactic_state revert(buffer<expr> & locals, tactic_state const & s) {
    lean_assert(s.goals());
    metavar_context mctx       = s.mctx();
    type_context ctx           = mk_type_context_for(s, mctx, transparency_mode::All);
    expr val                   = ctx.revert(locals.size(), locals.data(), head(s.goals()));
    locals.clear();
    expr new_g                 = get_app_args(val, locals);
    return set_mctx_goals(s, mctx, cons(new_g, tail(s.goals())));
}

vm_obj revert(list<name> const & ns, tactic_state const & s) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx         = g->get_context();
    buffer<expr> locals;
    for (name const & n : ns) {
        if (optional<local_decl> const & d = lctx.get_local_decl_from_user_name(n)) {
            locals.push_back(d->mk_ref());
        } else {
            return mk_tactic_exception(sstream() << "revert tactic failed, unknown '" << n << "' hypothesis", s);
        }
    }
    return mk_tactic_success(revert(locals, s));
}

vm_obj tactic_revert_lst(vm_obj const & ns, vm_obj const & s) {
    return revert(to_list_name(ns), to_tactic_state(s));
}

void initialize_revert_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "revert_lst"}), tactic_revert_lst);
}

void finalize_revert_tactic() {
}
}
