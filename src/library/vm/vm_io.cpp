/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
vm_obj put_str(vm_obj const & str, vm_obj const &) {
    std::cout << to_string(str);
    return mk_vm_unit();
}

vm_obj put_nat(vm_obj const & n, vm_obj const &) {
    if (is_simple(n))
        std::cout << cidx(n);
    else
        std::cout << to_mpz(n);
    return mk_vm_unit();
}

vm_obj get_line(vm_obj const &) {
    std::string str;
    std::getline(std::cin, str);
    return to_obj(str);
}

void initialize_vm_io() {
    DECLARE_VM_BUILTIN("put_str", put_str);
    DECLARE_VM_BUILTIN("put_nat", put_nat);
    DECLARE_VM_BUILTIN("get_line", get_line);
}

void finalize_vm_io() {
}
}
