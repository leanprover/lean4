/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_io.h"

namespace lean {
void initialize_vm_core_module() {
    initialize_vm_core();
    initialize_vm_nat();
    initialize_vm_io();
}
void finalize_vm_core_module() {
    finalize_vm_nat();
    finalize_vm_core();
    finalize_vm_io();
}

void initialize_vm_module() {
    initialize_vm();
}
void finalize_vm_module() {
    finalize_vm();
}
}
