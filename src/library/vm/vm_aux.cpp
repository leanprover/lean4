/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "util/timeit.h"
#include "library/trace.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"

namespace lean {
vm_obj vm_sorry() {
    auto & s = get_vm_state();
    throw exception(sstream() << s.call_stack_fn(s.call_stack_size() - 1)
                              << ": trying to evaluate sorry");
}

vm_obj vm_undefined_core(vm_obj const &, vm_obj const & message) {
    throw exception(to_string(message));
}

void initialize_vm_aux() {
    DECLARE_VM_BUILTIN("sorry",            vm_sorry);
    DECLARE_VM_BUILTIN("undefined_core",   vm_undefined_core);
}

void finalize_vm_aux() {
}
}
