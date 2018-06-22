/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "kernel/level.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_options.h"

namespace lean {
struct vm_level : public vm_external {
    level m_val;
    vm_level(level const & v):m_val(v) {}
    virtual ~vm_level() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_level(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_level(m_val); }
};

bool is_level(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_level*>(to_external(o));
}

level const & to_level(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_level*>(to_external(o)));
    return static_cast<vm_level*>(to_external(o))->m_val;
}

vm_obj to_obj(level const & n) {
    return mk_vm_external(new vm_level(n));
}

vm_obj level_zero() {
    return to_obj(mk_level_zero());
}

vm_obj level_succ(vm_obj const & o) {
    return to_obj(mk_succ(to_level(o)));
}

vm_obj level_max(vm_obj const & o1, vm_obj const & o2) {
    return to_obj(mk_max_core(to_level(o1), to_level(o2)));
}

vm_obj level_imax(vm_obj const & o1, vm_obj const & o2) {
    return to_obj(mk_imax_core(to_level(o1), to_level(o2)));
}

vm_obj level_param(vm_obj const & n) {
    return to_obj(mk_univ_param(to_name(n)));
}

vm_obj level_mvar(vm_obj const & n) {
    return to_obj(mk_univ_mvar(to_name(n)));
}

unsigned level_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    level const & l = to_level(o);
    switch (l.kind()) {
    case level_kind::Zero:
        break;
    case level_kind::Succ:
        data.push_back(to_obj(succ_of(l)));
        break;
    case level_kind::Max:
        data.push_back(to_obj(max_lhs(l)));
        data.push_back(to_obj(max_rhs(l)));
        break;
    case level_kind::IMax:
        data.push_back(to_obj(imax_lhs(l)));
        data.push_back(to_obj(imax_rhs(l)));
        break;
    case level_kind::Param:
        data.push_back(to_obj(param_id(l)));
        break;
    case level_kind::MVar:
        data.push_back(to_obj(mvar_id(l)));
        break;
    }
    return static_cast<unsigned>(l.kind());
}

void initialize_vm_level() {
    DECLARE_VM_BUILTIN(name({"lean", "level", "zero"}),             level_zero);
    DECLARE_VM_BUILTIN(name({"lean", "level", "succ"}),             level_succ);
    DECLARE_VM_BUILTIN(name({"lean", "level", "max"}),              level_max);
    DECLARE_VM_BUILTIN(name({"lean", "level", "imax"}),             level_imax);
    DECLARE_VM_BUILTIN(name({"lean", "level", "param"}),            level_param);
    DECLARE_VM_BUILTIN(name({"lean", "level", "mvar"}),             level_mvar);
    DECLARE_VM_CASES_BUILTIN(name({"lean", "level", "cases_on"}),   level_cases_on);
}

void finalize_vm_level() {
}
}
