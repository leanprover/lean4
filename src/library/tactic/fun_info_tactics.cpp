/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/fun_info.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/tactic/tactic_state.h"

namespace lean {
inline vm_obj bb(bool b) { return mk_vm_bool(b); }
/*
  structure param_info :=
  (specialized : bool)
  (is_implicit : bool)
  (is_inst_implicit : bool)
  (is_prop : bool)
  (is_subsingleton : bool)
  (has_fwd_deps : bool)
  (back_deps : list nat) -- previous parameters it depends on
*/
vm_obj to_obj(param_info const & info) {
    vm_obj args[7] = { bb(info.specialized()), bb(info.is_implicit()), bb(info.is_inst_implicit()),
                       bb(info.is_prop()), bb(info.is_subsingleton()), bb(info.has_fwd_deps()),
                       to_obj(info.get_back_deps()) };
    return mk_vm_constructor(0, 7, args);
}

vm_obj to_obj(list<param_info> const & ls) {
    return to_vm_list(ls, [&](param_info const & p) { return to_obj(p); });
}

/*
structure fun_info :=
(params      : list param_info)
(result_deps : list nat) -- parameters the result type depends on
*/
vm_obj to_obj(fun_info const & info) {
    return mk_vm_constructor(0, to_obj(info.get_params_info()), to_obj(info.get_result_deps()));
}

fun_info get_fun_info(type_context & ctx, expr const & fn);
/** \brief Return information assuming the function has only nargs.
    \pre nargs <= get_fun_info(ctx, fn).get_arity() */
fun_info get_fun_info(type_context & ctx, expr const & fn, unsigned nargs);
/** \brief Return information for the function application.
    This is more precise than \c get methods for dependent functions.

    Example: given (f : Pi (A : Type), A -> A), \c get_specialized_fun_info for

    f unit b

    returns a \c fun_info with two param_info
    1) m_specialized = true, m_is_dep = true
    2) m_subsingleton = true, m_deps = {0}

    The second argument is marked as subsingleton only because the resulting information
    is taking into account the first argument.

    \remark \c get and \c get_specialization return the same result for all but
    is_prop and is_subsingleton. */
fun_info get_specialized_fun_info(type_context & ctx, expr const & app);
unsigned get_specialization_prefix_size(type_context & ctx, expr const & fn, unsigned nargs);

#define TRY   LEAN_TACTIC_TRY
#define CATCH LEAN_TACTIC_CATCH(to_tactic_state(s))

static vm_obj mk_result(fun_info const & info, vm_obj const & s) {
    return mk_tactic_success(to_obj(info), to_tactic_state(s));
}

vm_obj tactic_get_fun_info(vm_obj const & fn, vm_obj const & s) {
    TRY;
    type_context_scope ctx(s);
    return mk_result(get_fun_info(ctx, to_expr(fn)), s);
    CATCH;
}

vm_obj tactic_get_fun_info_n(vm_obj const & fn, vm_obj const & n, vm_obj const & s) {
    TRY;
    type_context_scope ctx(s);
    return mk_result(get_fun_info(ctx, to_expr(fn), force_to_unsigned(n, 0)), s);
    CATCH;
}

vm_obj tactic_get_spec_fun_info(vm_obj const & app, vm_obj const & s) {
    TRY;
    type_context_scope ctx(s);
    return mk_result(get_specialized_fun_info(ctx, to_expr(app)), s);
    CATCH;
}

vm_obj tactic_get_spec_prefix_size(vm_obj const & fn, vm_obj const & n, vm_obj const & s) {
    TRY;
    type_context_scope ctx(s);
    return mk_tactic_success(mk_vm_nat(get_specialization_prefix_size(ctx, to_expr(fn), force_to_unsigned(n, 0))),
                             to_tactic_state(s));
    CATCH;
}

void initialize_fun_info_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "get_fun_info"}),           tactic_get_fun_info);
    DECLARE_VM_BUILTIN(name({"tactic", "get_fun_info_n"}),         tactic_get_fun_info_n);
    DECLARE_VM_BUILTIN(name({"tactic", "get_spec_fun_info"}),      tactic_get_spec_fun_info);
    DECLARE_VM_BUILTIN(name({"tactic", "get_spec_prefix_size"}),   tactic_get_spec_prefix_size);
}

void finalize_fun_info_tactics() {
}
}
