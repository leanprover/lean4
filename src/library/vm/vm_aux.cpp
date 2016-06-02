/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "util/timeit.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
vm_obj vm_timeit(vm_obj const &, vm_obj const & s, vm_obj const & fn) {
    std::string msg = to_string(s);
    timeit timer(std::cout, msg.c_str());
    return invoke(fn, mk_vm_unit());
}

void initialize_vm_aux() {
    DECLARE_VM_BUILTIN("timeit", vm_timeit);
}

void finalize_vm_aux() {
}
}
