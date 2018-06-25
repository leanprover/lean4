/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"

namespace lean {
/*
inductive reducibility_hint
| opaque  : reducibility_hint
| abbrev  : reducibility_hint
| regular : nat → bool → reducibility_hint
*/
vm_obj to_obj(reducibility_hints const & h) {
    switch (h.kind()) {
    case reducibility_hints_kind::Opaque:       return mk_vm_simple(0);
    case reducibility_hints_kind::Abbreviation: return mk_vm_simple(1);
    case reducibility_hints_kind::Regular:      return mk_vm_constructor(2, mk_vm_nat(h.get_height()));
    }
    lean_unreachable();
}

reducibility_hints to_reducibility_hints(vm_obj const & o) {
    switch (cidx(o)) {
    case 0: return reducibility_hints::mk_opaque();
    case 1: return reducibility_hints::mk_abbreviation();
    case 2: return reducibility_hints::mk_regular(force_to_unsigned(cfield(o, 0), 0));
    }
    lean_unreachable();
}

struct vm_declaration : public vm_external {
    declaration m_val;
    vm_declaration(declaration const & v):m_val(v) {}
    virtual ~vm_declaration() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_declaration(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_declaration(m_val); }
};

bool is_declaration(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_declaration*>(to_external(o));
}

declaration const & to_declaration(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_declaration*>(to_external(o)));
    return static_cast<vm_declaration*>(to_external(o))->m_val;
}

vm_obj to_obj(declaration const & n) {
    return mk_vm_external(new vm_declaration(n));
}

vm_obj declaration_defn(vm_obj const & n, vm_obj const & ls, vm_obj const & type, vm_obj const & value,
                        vm_obj const & hints, vm_obj const & meta) {
    return to_obj(mk_definition(to_name(n), to_names(ls), to_expr(type), to_expr(value), to_reducibility_hints(hints), to_bool(meta)));
}

vm_obj declaration_thm(vm_obj const & n, vm_obj const & ls, vm_obj const & type, vm_obj const & value) {
    return to_obj(mk_theorem(to_name(n), to_names(ls), to_expr(type), to_expr(value)));
}

vm_obj declaration_cnst(vm_obj const & n, vm_obj const & ls, vm_obj const & type, vm_obj const & meta) {
    return to_obj(mk_constant_assumption(to_name(n), to_names(ls), to_expr(type), to_bool(meta)));
}

vm_obj declaration_ax(vm_obj const & n, vm_obj const & ls, vm_obj const & type) {
    return to_obj(mk_axiom(to_name(n), to_names(ls), to_expr(type)));
}

unsigned declaration_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    declaration const & d = to_declaration(o);
    data.push_back(to_obj(d.get_name()));
    data.push_back(to_obj(d.get_univ_params()));
    data.push_back(to_obj(d.get_type()));
    if (d.is_theorem()) {
        data.push_back(to_obj(d.get_value()));
        return 1;
    } else if (d.is_axiom()) {
        return 3;
    } else if (d.is_definition()) {
        data.push_back(to_obj(d.get_value()));
        data.push_back(to_obj(d.get_hints()));
        data.push_back(mk_vm_bool(d.is_meta()));
        return 0;
    } else {
        lean_assert(d.is_constant_assumption());
        data.push_back(mk_vm_bool(d.is_meta()));
        return 2;
    }
}

/*
/- Instantiate a universe polymorphic declaration type with the given universes. -/
meta_constant declaration.instantiate_type_univ_params : declaration → list level → option expr
*/
vm_obj declaration_instantiate_type_univ_params(vm_obj const & _d, vm_obj const & _ls) {
    declaration const & d  = to_declaration(_d);
    levels ls = to_levels(_ls);
    if (d.get_num_univ_params() != length(ls))
        return mk_vm_none();
    else
        return mk_vm_some(to_obj(instantiate_type_univ_params(d, ls)));
}

/*
/- Instantiate a universe polymorphic declaration type with the given universes. -/
meta_constant declaration.instantiate_value_univ_params : declaration → list level → option expr
*/
vm_obj declaration_instantiate_value_univ_params(vm_obj const & _d, vm_obj const & _ls) {
    declaration const & d  = to_declaration(_d);
    levels ls = to_levels(_ls);
    if (!d.has_value() || d.get_num_univ_params() != length(ls))
        return mk_vm_none();
    else
        return mk_vm_some(to_obj(instantiate_value_univ_params(d, ls)));
}

void initialize_vm_declaration() {
    DECLARE_VM_BUILTIN(name({"declaration", "defn"}),           declaration_defn);
    DECLARE_VM_BUILTIN(name({"declaration", "thm"}),            declaration_thm);
    DECLARE_VM_BUILTIN(name({"declaration", "cnst"}),           declaration_cnst);
    DECLARE_VM_BUILTIN(name({"declaration", "ax"}),             declaration_ax);
    DECLARE_VM_BUILTIN(name({"declaration", "instantiate_type_univ_params"}), declaration_instantiate_type_univ_params);
    DECLARE_VM_BUILTIN(name({"declaration", "instantiate_value_univ_params"}), declaration_instantiate_value_univ_params);
    DECLARE_VM_CASES_BUILTIN(name({"declaration", "cases_on"}), declaration_cases_on);
}

void finalize_vm_declaration() {
}
}
