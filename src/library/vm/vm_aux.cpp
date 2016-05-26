/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/timeit.h"
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
static void vm_timeit(vm_state & s) {
    vm_obj const & msg  = s.get(-2);
    vm_obj const & fn   = s.get(-3);
    std::string msg_str = to_string(msg);
    timeit timer(std::cout, msg_str.c_str());
    s.push(mk_vm_unit());
    s.push(fn);
    s.apply();
}

void initialize_vm_aux() {
    declare_vm_builtin(get_timeit_name(), 3, vm_timeit);
}

void finalize_vm_aux() {
}
}
