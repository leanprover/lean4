/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"

namespace lean {
struct vm_declaration : public vm_external {
    declaration m_val;
    vm_declaration(declaration const & v):m_val(v) {}
    virtual void dealloc() override { this->~vm_declaration(); get_vm_allocator().deallocate(sizeof(vm_declaration), this); }
};

declaration const & to_declaration(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_declaration*>(to_external(o)));
    return static_cast<vm_declaration*>(to_external(o))->m_val;
}

vm_obj to_obj(declaration const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_declaration))) vm_declaration(n));
}

vm_obj declaration_def(vm_obj const & n, vm_obj const & ls, vm_obj const & type, vm_obj const & value,
                       vm_obj const & trusted) {
    return to_obj(mk_definition(to_name(n), to_list_name(ls), to_expr(type), to_expr(value), 0, true, to_bool(trusted)));
}

vm_obj declaration_thm(vm_obj const & n, vm_obj const & ls, vm_obj const & type, vm_obj const & value) {
    return to_obj(mk_theorem(to_name(n), to_list_name(ls), to_expr(type), to_expr(value), 0));
}

vm_obj declaration_cnst(vm_obj const & n, vm_obj const & ls, vm_obj const & type, vm_obj const & trusted) {
    return to_obj(mk_constant_assumption(to_name(n), to_list_name(ls), to_expr(type), to_bool(trusted)));
}

vm_obj declaration_ax(vm_obj const & n, vm_obj const & ls, vm_obj const & type) {
    return to_obj(mk_axiom(to_name(n), to_list_name(ls), to_expr(type)));
}

unsigned declaration_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    declaration const & d = to_declaration(o);
    data.push_back(to_obj(d.get_name()));
    data.push_back(to_obj(d.get_univ_params()));
    data.push_back(to_obj(d.get_type()));
    if (d.is_definition()) {
        data.push_back(to_obj(d.get_value()));
        data.push_back(mk_vm_bool(d.is_trusted()));
        return 0;
    } else if (d.is_theorem()) {
        data.push_back(to_obj(d.get_value()));
        return 1;
    } else if (d.is_constant_assumption()) {
        data.push_back(mk_vm_bool(d.is_trusted()));
        return 2;
    } else {
        lean_assert(d.is_axiom());
        return 3;
    }
}

void initialize_vm_declaration() {
    DECLARE_VM_BUILTIN(name({"declaration", "def"}),            declaration_def);
    DECLARE_VM_BUILTIN(name({"declaration", "thm"}),            declaration_thm);
    DECLARE_VM_BUILTIN(name({"declaration", "cnst"}),           declaration_cnst);
    DECLARE_VM_BUILTIN(name({"declaration", "ax"}),             declaration_ax);
    DECLARE_VM_CASES_BUILTIN(name({"declaration", "cases_on"}), declaration_cases_on);
}

void finalize_vm_declaration() {
}
}
