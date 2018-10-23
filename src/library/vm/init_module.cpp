/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_int.h"
#include "library/vm/vm_aux.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_array.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_platform.h"

namespace lean {
void initialize_vm_core_module() {
    initialize_vm_core();
    initialize_vm_nat();
    initialize_vm_int();
    initialize_vm_aux();
    initialize_vm_io();
    initialize_vm_array();
    initialize_vm_string();
    initialize_vm_platform();
}

void finalize_vm_core_module() {
    finalize_vm_platform();
    finalize_vm_string();
    finalize_vm_array();
    finalize_vm_io();
    finalize_vm_aux();
    finalize_vm_int();
    finalize_vm_nat();
    finalize_vm_core();
}

void initialize_vm_module() {
    initialize_vm();
    initialize_vm_array_builtin_idxs();
}
void finalize_vm_module() {
    finalize_vm();
}
}
