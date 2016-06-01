/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/constants.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
struct vm_name : public vm_external {
    name m_val;
    vm_name(name const & v):m_val(v) {}
    virtual ~vm_name() {}
};

name const & to_name(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_name*>(to_external(o)));
    return static_cast<vm_name*>(to_external(o))->m_val;
}

vm_obj to_obj(name const & n) {
    return mk_vm_external(new vm_name(n));
}

static vm_obj name_anonymous() {
    return to_obj(name());
}

static vm_obj name_mk_string(vm_obj const & s, vm_obj const & n) {
    std::string str = to_string(s);
    return to_obj(name(to_name(n), str.c_str()));
}

static vm_obj name_mk_numeral(vm_obj const & num, vm_obj const & n) {
    unsigned idx;
    if (is_simple(num)) {
        idx = cidx(num);
    } else {
        idx = to_mpz(num).get_unsigned_int();
    }
    return to_obj(name(to_name(n), idx));
}

void initialize_vm_name() {
    declare_vm_builtin(get_name_anonymous_name(),   name_anonymous);
    declare_vm_builtin(get_name_mk_string_name(),   name_mk_string);
    declare_vm_builtin(get_name_mk_numeral_name(),  name_mk_numeral);
}

void finalize_vm_name() {
}
}
