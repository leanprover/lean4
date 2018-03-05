/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/fun_info.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"

namespace lean {
inline vm_obj bb(bool b) { return mk_vm_bool(b); }
/*
  structure param_info :=
  (is_implicit : bool)
  (is_inst_implicit : bool)
  (is_prop : bool)
  (has_fwd_deps : bool)
  (back_deps : list nat) -- previous parameters it depends on
*/
vm_obj to_obj(param_info const & info) {
    vm_obj args[5] = { bb(info.is_implicit()), bb(info.is_inst_implicit()),
                       bb(info.is_prop()), bb(info.has_fwd_deps()),
                       to_obj(info.get_back_deps()) };
    return mk_vm_constructor(0, 5, args);
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

vm_obj to_obj(ss_param_info const & info) {
    return mk_vm_constructor(0, bb(info.specialized()), bb(info.is_subsingleton()));
}

vm_obj to_obj(list<ss_param_info> const & ls) {
    return to_vm_list(ls, [&](ss_param_info const & p) { return to_obj(p); });
}

#define TRY   LEAN_TACTIC_TRY
#define CATCH LEAN_TACTIC_CATCH(tactic::to_state(s))

static vm_obj mk_result(fun_info const & info, vm_obj const & s) {
    return tactic::mk_success(to_obj(info), tactic::to_state(s));
}

static vm_obj mk_result(list<ss_param_info> const & info, vm_obj const & s) {
    return tactic::mk_success(to_obj(info), tactic::to_state(s));
}

vm_obj tactic_get_fun_info(vm_obj const & fn, vm_obj const & n, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    if (is_none(n)) {
        return mk_result(get_fun_info(ctx, to_expr(fn)), s);
    } else {
        return mk_result(get_fun_info(ctx, to_expr(fn), force_to_unsigned(get_some_value(n), 0)), s);
    }
    CATCH;
}

vm_obj tactic_get_subsingleton_info(vm_obj const & fn, vm_obj const & n, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    if (is_none(n)) {
        return mk_result(get_subsingleton_info(ctx, to_expr(fn)), s);
    } else {
        return mk_result(get_subsingleton_info(ctx, to_expr(fn), force_to_unsigned(get_some_value(n), 0)), s);
    }
    CATCH;
}

vm_obj tactic_get_spec_subsingleton_info(vm_obj const & app, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    return mk_result(get_specialized_subsingleton_info(ctx, to_expr(app)), s);
    CATCH;
}

vm_obj tactic_get_spec_prefix_size(vm_obj const & fn, vm_obj const & n, vm_obj const & m, vm_obj const & s) {
    TRY;
    type_context_old ctx = mk_type_context_for(s, m);
    return tactic::mk_success(mk_vm_nat(get_specialization_prefix_size(ctx, to_expr(fn), force_to_unsigned(n, 0))),
                             tactic::to_state(s));
    CATCH;
}

void initialize_fun_info_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "get_fun_info"}),               tactic_get_fun_info);
    DECLARE_VM_BUILTIN(name({"tactic", "get_subsingleton_info"}),      tactic_get_subsingleton_info);
    DECLARE_VM_BUILTIN(name({"tactic", "get_spec_subsingleton_info"}), tactic_get_spec_subsingleton_info);
    DECLARE_VM_BUILTIN(name({"tactic", "get_spec_prefix_size"}),       tactic_get_spec_prefix_size);
}

void finalize_fun_info_tactics() {
}
}
