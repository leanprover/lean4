/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
namespace lean {
static vm_obj dummy_binary_op(vm_obj const &, vm_obj const &) {
    throw exception("thunk support has not been implemented in the old VM");
}

static vm_obj dummy_quad_op(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &) {
    throw exception("thunk support has not been implemented in the old VM");
}

void initialize_vm_thunk() {
    DECLARE_VM_BUILTIN(name({"thunk", "mk"}),         dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"thunk", "get"}),        dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"thunk", "pure"}),       dummy_binary_op);
    DECLARE_VM_BUILTIN(name({"thunk", "bind"}),       dummy_quad_op);
    DECLARE_VM_BUILTIN(name({"thunk", "map"}),        dummy_quad_op);
}

void finalize_vm_thunk() {
}
}
