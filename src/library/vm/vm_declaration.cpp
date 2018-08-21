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

vm_obj declaration_defn(vm_obj const & val) {
    return to_obj(mk_definition(to_name(cfield(cfield(val, 0), 0)),
                                to_names(cfield(cfield(val, 0), 1)),
                                to_expr(cfield(cfield(val, 0), 2)),
                                to_expr(cfield(val, 1)),
                                to_reducibility_hints(cfield(val, 2)),
                                to_bool(cfield(val, 3))));
}

vm_obj declaration_thm(vm_obj const & val) {
    return to_obj(mk_theorem(to_name(cfield(cfield(val, 0), 0)),
                             to_names(cfield(cfield(val, 0), 1)),
                             to_expr(cfield(cfield(val, 0), 2)),
                             to_expr(cfield(val, 1))));
}

vm_obj declaration_ax(vm_obj const & val) {
    return to_obj(mk_axiom(to_name(cfield(cfield(val, 0), 0)),
                           to_names(cfield(cfield(val, 0), 1)),
                           to_expr(cfield(cfield(val, 0), 2)),
                           to_bool(cfield(val, 1))));
}

vm_obj mk_declaration_val(declaration const & d) {
    return mk_vm_constructor(0, to_obj(d.get_name()), to_obj(d.get_univ_params()), to_obj(d.get_type()));
}

unsigned declaration_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    declaration const & d = to_declaration(o);
    switch (d.kind()) {
    case declaration_kind::Definition:
        data.push_back(mk_vm_constructor(0, mk_declaration_val(d), to_obj(d.get_value()), to_obj(d.get_hints()), mk_vm_bool(d.is_meta())));
        break;
    case declaration_kind::Axiom:
        data.push_back(mk_vm_constructor(0, mk_declaration_val(d), mk_vm_bool(d.is_meta())));
        break;
    case declaration_kind::Theorem:
        data.push_back(mk_vm_constructor(0, mk_declaration_val(d), to_obj(d.get_value())));
        break;
    case declaration_kind::Inductive:   lean_unreachable(); // TODO(Leo):
    case declaration_kind::Constructor: lean_unreachable(); // TODO(Leo):
    case declaration_kind::Recursor:    lean_unreachable(); // TODO(Leo):
    }
    return static_cast<unsigned>(d.kind());
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
    DECLARE_VM_BUILTIN(name({"lean", "constant_info", "defn_info"}),  declaration_defn);
    DECLARE_VM_BUILTIN(name({"lean", "constant_info", "thm_info"}),   declaration_thm);
    DECLARE_VM_BUILTIN(name({"lean", "constant_info", "axiom_info"}), declaration_ax);
    DECLARE_VM_BUILTIN(name({"lean", "constant_info", "instantiate_type_univ_params"}),  declaration_instantiate_type_univ_params);
    DECLARE_VM_BUILTIN(name({"lean", "constant_info", "instantiate_value_univ_params"}), declaration_instantiate_value_univ_params);
    DECLARE_VM_CASES_BUILTIN(name({"lean", "constant_info", "cases_on"}), declaration_cases_on);
}

void finalize_vm_declaration() {
}
}
