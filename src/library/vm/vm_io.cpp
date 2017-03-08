/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
vm_obj mk_io_result(vm_obj const & r) {
    return mk_vm_pair(r, mk_vm_unit());
}

vm_obj io_put_str(vm_obj const & str, vm_obj const &) {
    get_global_ios().get_regular_stream() << to_string(str);
    return mk_io_result(mk_vm_unit());
}

vm_obj io_get_line(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        throw exception("get_line: cannot read from stdin in server mode");
    std::string str;
    std::getline(std::cin, str);
    return mk_io_result(to_obj(str));
}

vm_obj io_return(vm_obj const &, vm_obj const & a, vm_obj const &) {
    return mk_io_result(a);
}

vm_obj io_bind(vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const & b, vm_obj const &) {
    return invoke(b, cfield(invoke(a, mk_vm_unit()), 0), mk_vm_unit());
}

vm_obj io_map(vm_obj const &, vm_obj const &, vm_obj const & f, vm_obj const & a, vm_obj const &) {
    return mk_io_result(invoke(f, cfield(invoke(a, mk_vm_unit()), 0)));
}

void initialize_vm_io() {
    DECLARE_VM_BUILTIN(name({"io", "put_str"}),  io_put_str);
    DECLARE_VM_BUILTIN(name({"io", "get_line"}), io_get_line);
    DECLARE_VM_BUILTIN(name({"io", "return"}),   io_return);
    DECLARE_VM_BUILTIN(name({"io", "bind"}),     io_bind);
    DECLARE_VM_BUILTIN(name({"io", "map"}),      io_map);
}

void finalize_vm_io() {
}
}
