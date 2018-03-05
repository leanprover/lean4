/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"

namespace lean {
expr revert(environment const & env, options const & opts, metavar_context & mctx, expr const & mvar, buffer<expr> & locals,
            bool preserve_locals_order) {
    optional<metavar_decl> g   = mctx.find_metavar_decl(mvar);
    lean_assert(g);
    type_context_old ctx           = mk_type_context_for(env, opts, mctx, g->get_context(), transparency_mode::All);
    expr val                   = ctx.revert(locals, mvar, preserve_locals_order);
    expr new_g                 = get_app_fn(val);
    mctx                       = ctx.mctx();
    return new_g;
}

tactic_state revert(buffer<expr> & locals, tactic_state const & s, bool preserve_locals_order) {
    lean_assert(s.goals());
    metavar_context mctx = s.mctx();
    expr new_g = revert(s.env(), s.get_options(), mctx, head(s.goals()), locals, preserve_locals_order);
    return set_mctx_goals(s, mctx, cons(new_g, tail(s.goals())));
}

vm_obj revert(list<expr> const & ls, tactic_state const & s, bool preserve_locals_order) {
    try {
        optional<metavar_decl> g   = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        local_context lctx         = g->get_context();
        buffer<expr> locals;
        for (expr const & l : ls) {
            if (lctx.find_local_decl(l)) {
                locals.push_back(l);
            } else {
                return tactic::mk_exception(sstream() << "revert tactic failed, unknown '"
                                            << mlocal_pp_name(l) << "' hypothesis", s);
            }
        }
        tactic_state new_s = revert(locals, s, preserve_locals_order);
        return tactic::mk_success(mk_vm_nat(locals.size()), new_s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_revert_lst(vm_obj const & ns, vm_obj const & s) {
    bool preserve_locals_order = false;
    return revert(to_list_expr(ns), tactic::to_state(s), preserve_locals_order);
}

void initialize_revert_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "revert_lst"}), tactic_revert_lst);
}

void finalize_revert_tactic() {
}
}
