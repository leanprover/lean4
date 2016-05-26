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
static void put_str(vm_state & s) {
    vm_obj const & str = s.get(-1);
    std::cout << to_string(str);
    return s.push(mk_vm_unit());
}

static void put_nat(vm_state & s) {
    vm_obj const & n = s.get(-1);
    if (is_simple(n))
        std::cout << cidx(n);
    else
        std::cout << to_mpz(n);
    return s.push(mk_vm_unit());
}

static void get_line(vm_state & s) {
    std::string str;
    std::getline(std::cin, str);
    return s.push(to_obj(str));
}

void initialize_vm_io() {
    declare_vm_builtin(get_put_str_name(),   2, put_str);
    declare_vm_builtin(get_put_nat_name(),   2, put_nat);
    declare_vm_builtin(get_get_line_name(),  1, get_line);
}

void finalize_vm_io() {
}
}
