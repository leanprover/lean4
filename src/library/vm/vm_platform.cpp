/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"

namespace lean {
vm_obj system_platform_nbits() {
    return mk_vm_nat(8 * sizeof(size_t));
}

void initialize_vm_platform() {
    DECLARE_VM_BUILTIN(name({"system", "platform", "nbits"}), system_platform_nbits);
}

void finalize_vm_platform() {
}
}
