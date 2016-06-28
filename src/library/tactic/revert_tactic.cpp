/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"

namespace lean {
tactic_state revert(buffer<expr> & locals, tactic_state const & s) {
    lean_assert(s.goals());
    type_context ctx           = mk_type_context_for(s, transparency_mode::All);
    expr val                   = ctx.revert(locals, head(s.goals()));
    expr new_g                 = get_app_fn(val);
    return set_mctx_goals(s, ctx.mctx(), cons(new_g, tail(s.goals())));
}

vm_obj revert(list<expr> const & ls, tactic_state const & s) {
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx         = g->get_context();
    buffer<expr> locals;
    for (expr const & l : ls) {
        if (lctx.get_local_decl(l)) {
            locals.push_back(l);
        } else {
            return mk_tactic_exception(sstream() << "revert tactic failed, unknown '" << local_pp_name(l) << "' hypothesis", s);
        }
    }
    tactic_state new_s = revert(locals, s);
    return mk_tactic_success(mk_vm_nat(locals.size()), new_s);
}

vm_obj tactic_revert_lst(vm_obj const & ns, vm_obj const & s) {
    return revert(to_list_expr(ns), to_tactic_state(s));
}

void initialize_revert_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "revert_lst"}), tactic_revert_lst);
}

void finalize_revert_tactic() {
}
}
