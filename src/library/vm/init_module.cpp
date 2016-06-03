/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_aux.h"

namespace lean {
void initialize_vm_core_module() {
    initialize_vm_core();
    initialize_vm_nat();
    initialize_vm_io();
    initialize_vm_name();
    initialize_vm_options();
    initialize_vm_format();
    initialize_vm_aux();
}
void finalize_vm_core_module() {
    finalize_vm_aux();
    finalize_vm_format();
    finalize_vm_options();
    finalize_vm_name();
    finalize_vm_io();
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
