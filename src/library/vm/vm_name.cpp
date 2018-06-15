/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "library/util.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_ordering.h"
#include "library/vm/vm_list.h"

namespace lean {
struct vm_name : public vm_external {
    name m_val;
    vm_name(name const & v):m_val(v) {}
    virtual ~vm_name() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_name(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_name(m_val); }
};

bool is_name(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_name*>(to_external(o));
}

name const & to_name(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_name *>(to_external(o)));
    return static_cast<vm_name*>(to_external(o))->m_val;
}

vm_obj to_obj(name const & n) {
    return mk_vm_external(new vm_name(n));
}

vm_obj name_anonymous() {
    return to_obj(name());
}

vm_obj name_mk_string(vm_obj const & n, vm_obj const & s) {
    std::string str = to_string(s);
    return to_obj(name(to_name(n), str.c_str()));
}

vm_obj name_mk_numeral(vm_obj const & n, vm_obj const & num) {
    return to_obj(name(to_name(n), to_unsigned(num)));
}

unsigned name_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    name const & n = to_name(o);
    if (n.is_anonymous()) {
        return 0;
    } else if (n.is_string()) {
        data.push_back(to_obj(n.get_prefix()));
        data.push_back(to_obj(n.get_string().to_std_string()));
        return 1;
    } else {
        data.push_back(to_obj(n.get_prefix()));
        data.push_back(mk_vm_nat(n.get_numeral().to_mpz()));
        return 2;
    }
}

vm_obj name_has_decidable_eq(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(to_name(o1) == to_name(o2));
}

vm_obj name_cmp(vm_obj const & o1, vm_obj const & o2) {
    return int_to_ordering(quick_cmp(to_name(o1), to_name(o2)));
}

vm_obj name_lex_cmp(vm_obj const & o1, vm_obj const & o2) {
    return int_to_ordering(cmp(to_name(o1), to_name(o2)));
}

vm_obj name_append_after(vm_obj const & n, vm_obj const & i) {
    return to_obj(to_name(n).append_after(force_to_unsigned(i, 0)));
}

vm_obj name_append(vm_obj const & n1, vm_obj const & n2) {
    return to_obj(to_name(n1) + to_name(n2));
}

vm_obj name_is_internal(vm_obj const & n) {
    return mk_vm_bool(is_internal_name(to_name(n)));
}

void initialize_vm_name() {
    DECLARE_VM_BUILTIN(name({"lean", "name", "anonymous"}),        name_anonymous);
    DECLARE_VM_BUILTIN(name({"lean", "name", "mk_string"}),        name_mk_string);
    DECLARE_VM_BUILTIN(name({"lean", "name", "mk_numeral"}),       name_mk_numeral);
    DECLARE_VM_BUILTIN(name({"lean", "name", "has_decidable_eq"}), name_has_decidable_eq);
    DECLARE_VM_BUILTIN(name({"name", "cmp"}),              name_cmp);
    DECLARE_VM_BUILTIN(name({"name", "lex_cmp"}),          name_lex_cmp);
    DECLARE_VM_BUILTIN(name({"name", "append"}),           name_append);
    DECLARE_VM_BUILTIN(name({"lean", "name", "is_internal"}),      name_is_internal);
    DECLARE_VM_BUILTIN(name({"lean", "name", "append_after"}),     name_append_after);
    DECLARE_VM_CASES_BUILTIN(name({"lean", "name", "cases_on"}),   name_cases_on);
}

void finalize_vm_name() {
}
}
