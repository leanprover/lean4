/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/tactic_state.h"

namespace lean {
static vm_obj eval(expr const & A, expr const & a, tactic_state const & s) {
    LEAN_TACTIC_TRY;
    if (has_local(a) || !closed(a))
        return mk_tactic_exception("invalid eval_expr, expression must be closed", s);
    if (is_constant(a)) {
        type_context ctx = mk_type_context_for(s);
        if (!ctx.is_def_eq(A, ctx.infer(a)))
            return mk_tactic_exception("invalid eval_expr, type mismatch", s);
        vm_obj r = get_vm_state().get_constant(const_name(a));
        return mk_tactic_success(r, s);
    } else {
        vm_state & S = get_vm_state();
        environment aux_env = S.env();
        name eval_aux_name = mk_tagged_fresh_name("_eval_expr");
        auto cd = check(aux_env, mk_definition(aux_env, eval_aux_name, {}, A, a, true, false));
        aux_env = aux_env.add(cd);
        aux_env = vm_compile(aux_env, aux_env.get(eval_aux_name));
        S.update_env(aux_env);
        vm_obj r = S.get_constant(eval_aux_name);
        return mk_tactic_success(r, s);
    }
    LEAN_TACTIC_CATCH(s);
}

static vm_obj tactic_eval_expr(vm_obj const &, vm_obj const & A, vm_obj const & a, vm_obj const & s) {
    return eval(to_expr(A), to_expr(a), to_tactic_state(s));
}

void initialize_eval() {
    DECLARE_VM_BUILTIN(name({"tactic", "eval_expr"}), tactic_eval_expr);
}

void finalize_eval() {
}
}
