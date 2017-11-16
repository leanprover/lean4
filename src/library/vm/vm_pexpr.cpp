/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/choice.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "frontends/lean/util.h"
#include "frontends/lean/structure_instance.h"

namespace lean {
vm_obj pexpr_of_expr(vm_obj const & e) {
    return to_obj(mk_as_is(to_expr(e)));
}

vm_obj pexpr_is_placeholder(vm_obj const & e) {
    return mk_vm_bool(is_placeholder(to_expr(e)));
}

vm_obj pexpr_mk_placeholder() {
    return to_obj(mk_expr_placeholder());
}

vm_obj pexpr_mk_explicit(vm_obj const & e) {
    return to_obj(mk_explicit(to_expr(e)));
}

vm_obj pexpr_mk_field_macro(vm_obj const & e, vm_obj const & fname) {
    return to_obj(mk_field_notation(to_expr(e), to_name(fname)));
}

vm_obj pexpr_is_choice_macro(vm_obj const & e) {
    return mk_vm_bool(is_choice(to_expr(e)));
}

vm_obj pexpr_mk_structure_instance(vm_obj const & info) {
    name struct_name;
    buffer<name> field_names;
    buffer<expr> field_values;
    buffer<expr> sources;
    if (!is_none(cfield(info, 0))) {
        struct_name = to_name(get_some_value(cfield(info, 0)));
    }
    to_buffer_name(cfield(info, 1), field_names);
    to_buffer_expr(cfield(info, 2), field_values);
    to_buffer_expr(cfield(info, 3), sources);
    return to_obj(mk_structure_instance(struct_name, field_names, field_values, sources));
}

vm_obj pexpr_get_structure_instance_info(vm_obj const & e) {
    if (!is_structure_instance(to_expr(e))) {
        return mk_vm_none();
    }
    auto info = get_structure_instance_info(to_expr(e));
    optional<name> opt_struct_name;
    if (info.m_struct_name) {
        opt_struct_name = info.m_struct_name;
    }
    return mk_vm_some(mk_vm_constructor(0, to_obj(opt_struct_name), to_obj(info.m_field_names),
                                        to_obj(info.m_field_values), to_obj(info.m_sources)));
}

void initialize_vm_pexpr() {
    DECLARE_VM_BUILTIN(name({"pexpr", "of_expr"}),        pexpr_of_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "is_placeholder"}), pexpr_is_placeholder);
    DECLARE_VM_BUILTIN(name({"pexpr", "mk_placeholder"}), pexpr_mk_placeholder);

    DECLARE_VM_BUILTIN(name("pexpr", "mk_explicit"),      pexpr_mk_explicit);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_field_macro"),   pexpr_mk_field_macro);

    DECLARE_VM_BUILTIN(name("pexpr", "is_choice_macro"),  pexpr_is_choice_macro);

    DECLARE_VM_BUILTIN(name("pexpr", "mk_structure_instance"), pexpr_mk_structure_instance);
    DECLARE_VM_BUILTIN(name("pexpr", "get_structure_instance_info"), pexpr_get_structure_instance_info);
}

void finalize_vm_pexpr() {
}
}
