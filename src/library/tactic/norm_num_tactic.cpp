/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura
*/
#include "library/norm_num.h"
#include "library/type_context.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj tactic_norm_num(vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    type_context_old ctx = mk_type_context_for(s);
    try {
        pair<expr, expr> p = mk_norm_num(ctx, to_expr(e));
        return tactic::mk_success(mk_vm_pair(to_obj(p.first), to_obj(p.second)), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_norm_num_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "norm_num"}), tactic_norm_num);
}
void finalize_norm_num_tactic() {
}
}
