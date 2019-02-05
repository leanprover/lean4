/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
namespace lean {
static vm_obj dummy_unary_op(vm_obj const &) {
    throw exception("name object support has not been implemented in the old VM");
}

static vm_obj dummy_binary_op(vm_obj const &, vm_obj const &) {
    throw exception("name object support has not been implemented in the old VM");
}

void initialize_vm_name() {
    DECLARE_VM_BUILTIN(name({"lean", "name", "hash"}),        dummy_unary_op);
    DECLARE_VM_BUILTIN(name({"lean", "name", "mk_string"}),   dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"lean", "name", "mk_numeral"}),  dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"lean", "name", "dec_eq"}),      dummy_binary_op);
}

void finalize_vm_name() {
}
}
