/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
static vm_obj put_str(vm_obj const & str, vm_obj const &) {
    std::cout << to_string(str);
    return mk_vm_unit();
}

static vm_obj put_nat(vm_obj const & n, vm_obj const &) {
    if (is_simple(n))
        std::cout << cidx(n);
    else
        std::cout << to_mpz(n);
    return mk_vm_unit();
}

static vm_obj get_line(vm_obj const &) {
    std::string str;
    std::getline(std::cin, str);
    return to_obj(str);
}

void initialize_vm_io() {
    declare_vm_builtin(get_put_str_name(),   put_str);
    declare_vm_builtin(get_put_nat_name(),   put_nat);
    declare_vm_builtin(get_get_line_name(),  get_line);
}

void finalize_vm_io() {
}
}
