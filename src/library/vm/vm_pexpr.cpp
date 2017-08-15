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
#include "frontends/lean/util.h"

namespace lean {
vm_obj pexpr_of_expr(vm_obj const & e) {
    return to_obj(mk_as_is(to_expr(e)));
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

void initialize_vm_pexpr() {
    DECLARE_VM_BUILTIN(name({"pexpr", "of_expr"}),        pexpr_of_expr);
    DECLARE_VM_BUILTIN(name({"pexpr", "mk_placeholder"}), pexpr_mk_placeholder);

    DECLARE_VM_BUILTIN(name("pexpr", "mk_explicit"),      pexpr_mk_explicit);
    DECLARE_VM_BUILTIN(name("pexpr", "mk_field_macro"),   pexpr_mk_field_macro);

    DECLARE_VM_BUILTIN(name("pexpr", "is_choice_macro"),  pexpr_is_choice_macro);
}

void finalize_vm_pexpr() {
}
}
