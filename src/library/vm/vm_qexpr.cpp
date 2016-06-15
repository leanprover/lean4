/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"

namespace lean {
vm_obj qexpr_subst(vm_obj const & _e1, vm_obj const & _e2) {
    expr const & e1 = to_expr(_e1);
    expr const & e2 = to_expr(_e2);
    if (is_lambda(e1)) {
        return to_obj(instantiate(binding_body(e1), e2));
    } else {
        return to_obj(e1);
    }
}

vm_obj qexpr_of_expr(vm_obj const & e) {
    // TODO(Leo): use "as_is" macro
    return e;
}

vm_obj expr_to_string(vm_obj const &);

vm_obj qexpr_to_string(vm_obj const & e) {
    return expr_to_string(e);
}

void initialize_vm_qexpr() {
    DECLARE_VM_BUILTIN(name({"qexpr", "subst"}),        qexpr_subst);
    DECLARE_VM_BUILTIN(name({"qexpr", "of_expr"}),      qexpr_of_expr);
    DECLARE_VM_BUILTIN(name({"qexpr", "to_string"}),    qexpr_to_string);
}

void finalize_vm_qexpr() {
}
}
