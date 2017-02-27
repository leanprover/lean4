/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/tactic_state.h"

namespace lean {
static vm_obj eval(expr const & A, expr a, tactic_state const & s) {
    LEAN_TACTIC_TRY;
    metavar_context mctx = s.mctx();
    a = mctx.instantiate_mvars(a);
    if (has_local(a) || !closed(a))
        return tactic::mk_exception("invalid eval_expr, expression must be closed", s);
    if (is_constant(a)) {
        type_context ctx = mk_type_context_for(s);
        if (!ctx.is_def_eq(A, ctx.infer(a)))
            return tactic::mk_exception("invalid eval_expr, type mismatch", s);
        vm_obj r = get_vm_state().get_constant(const_name(a));
        return tactic::mk_success(r, s);
    } else {
        vm_state & S = get_vm_state();
        environment aux_env = S.env();
        name eval_aux_name = mk_tagged_fresh_name("_eval_expr");
        /* We use nested_exception_without_pos to make sure old position information nested in 'a' is used
           in type error messages. */
        try {
            auto cd = check(aux_env, mk_definition(aux_env, eval_aux_name, {}, A, a, true, false));
            aux_env = aux_env.add(cd);
        } catch (kernel_exception & ex) {
            return tactic::mk_exception(nested_exception_without_pos("eval_expr failed due to type error", ex), s);
        }
        try {
            aux_env = vm_compile(aux_env, aux_env.get(eval_aux_name));
        } catch (exception & ex) {
            return tactic::mk_exception(nested_exception_without_pos("eval_expr failed to compile given expression into bytecode", ex), s);
        }
        S.update_env(aux_env);
        vm_obj r = S.get_constant(eval_aux_name);
        return tactic::mk_success(r, s);
    }
    LEAN_TACTIC_CATCH(s);
}

static vm_obj tactic_eval_expr(vm_obj const &, vm_obj const & A, vm_obj const & a, vm_obj const & s) {
    return eval(to_expr(A), to_expr(a), tactic::to_state(s));
}

void initialize_eval() {
    DECLARE_VM_BUILTIN(name({"tactic", "eval_expr"}), tactic_eval_expr);
}

void finalize_eval() {
}
}
