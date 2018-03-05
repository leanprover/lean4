/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/tactic_state.h"

namespace lean {
static vm_obj eval(expr const & A, expr a, tactic_state const & s) {
    metavar_context mctx = s.mctx();
    a = mctx.instantiate_mvars(a);
    if (has_local(a) || !closed(a))
        return tactic::mk_exception("invalid eval_expr, expression must be closed", s);
    if (is_constant(a)) {
        type_context_old ctx = mk_type_context_for(s);
        if (!ctx.is_def_eq(A, ctx.infer(a)))
            return tactic::mk_exception("invalid eval_expr, type mismatch", s);
        vm_obj r = get_vm_state().get_constant(const_name(a));
        return tactic::mk_success(r, s);
    } else {
        vm_state & S = get_vm_state();
        environment aux_env = S.env();
        name eval_aux_name = mk_unused_name(aux_env, "_eval_expr");
        try {
            auto cd = check(aux_env, mk_definition(aux_env, eval_aux_name, {}, A, a, true, false));
            aux_env = aux_env.add(cd);
        } catch (definition_type_mismatch_exception & ex) {
            expr given_type = ex.get_given_type();
            return tactic::mk_exception([=]() {
                io_state_stream ios = tout();
                formatter fmt = ios.get_formatter();
                return format("type error at eval_expr, argument ") + pp_type_mismatch(fmt, given_type, A);
            }, s);
        } catch (kernel_exception & ex) {
            /* We use nested_exception_without_pos to make sure old position information nested in 'a' is not used
               in type error messages. */
            return tactic::mk_exception(nested_exception_without_pos("eval_expr failed", ex), s);
        }
        try {
            aux_env = vm_compile(aux_env, aux_env.get(eval_aux_name));
        } catch (exception & ex) {
            return tactic::mk_exception(nested_exception_without_pos("eval_expr failed to compile given expression into bytecode", ex), s);
        }
        S.update_env(aux_env);
        /*
         * We can't catch exceptions here unless we restore the vm_state to a valid state.
         */
        vm_obj r = S.get_constant(eval_aux_name);
        return tactic::mk_success(r, s);
    }
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
