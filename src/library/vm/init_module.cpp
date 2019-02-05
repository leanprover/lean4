/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_int.h"
#include "library/vm/vm_uint.h"
#include "library/vm/vm_aux.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_thunk.h"
#include "library/vm/vm_name.h"

namespace lean {
void initialize_vm_core_module() {
    initialize_vm_core();
    initialize_vm_nat();
    initialize_vm_int();
    initialize_vm_aux();
    initialize_vm_io();
    initialize_vm_string();
    initialize_vm_uint();
    initialize_vm_thunk();
    initialize_vm_name();
}

void finalize_vm_core_module() {
    finalize_vm_name();
    finalize_vm_thunk();
    finalize_vm_uint();
    finalize_vm_string();
    finalize_vm_io();
    finalize_vm_aux();
    finalize_vm_int();
    finalize_vm_nat();
    finalize_vm_core();
}

void initialize_vm_module() {
    initialize_vm();
}
void finalize_vm_module() {
    finalize_vm();
}
}
