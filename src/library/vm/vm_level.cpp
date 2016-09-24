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
#include "library/vm/vm_list.h"

namespace lean {
struct vm_level : public vm_external {
    level m_val;
    vm_level(level const & v):m_val(v) {}
    virtual void dealloc() override { this->~vm_level(); get_vm_allocator().deallocate(sizeof(vm_level), this); }
};

level const & to_level(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_level*>(to_external(o)));
    return static_cast<vm_level*>(to_external(o))->m_val;
}

vm_obj to_obj(level const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_level))) vm_level(n));
}

vm_obj level_zero() {
    return to_obj(mk_level_zero());
}

vm_obj level_succ(vm_obj const & o) {
    return to_obj(mk_succ(to_level(o)));
}

vm_obj level_max(vm_obj const & o1, vm_obj const & o2) {
    return to_obj(mk_max(to_level(o1), to_level(o2)));
}

vm_obj level_imax(vm_obj const & o1, vm_obj const & o2) {
    return to_obj(mk_imax(to_level(o1), to_level(o2)));
}

vm_obj level_param(vm_obj const & n) {
    return to_obj(mk_param_univ(to_name(n)));
}

vm_obj level_global(vm_obj const & n) {
    return to_obj(mk_global_univ(to_name(n)));
}

vm_obj level_mvar(vm_obj const & n) {
    return to_obj(mk_meta_univ(to_name(n)));
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
    case level_kind::Global:
        data.push_back(to_obj(global_id(l)));
        break;
    case level_kind::Meta:
        data.push_back(to_obj(meta_id(l)));
        break;
    }
    return static_cast<unsigned>(l.kind());
}

vm_obj level_has_decidable_eq(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(to_level(o1) == to_level(o2));
}

vm_obj level_lt(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_lt(to_level(o1), to_level(o2), true));
}

vm_obj level_lex_lt(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_lt(to_level(o1), to_level(o2), false));
}

vm_obj level_eqv(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_equivalent(to_level(o1), to_level(o2)));
}

vm_obj level_normalize(vm_obj const & o) {
    return to_obj(normalize(to_level(o)));
}

vm_obj level_occurs(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(occurs(to_level(o1), to_level(o2)));
}

vm_obj level_to_format(vm_obj const & l, vm_obj const & o) {
    return to_obj(pp(to_level(l), to_options(o)));
}

vm_obj level_to_string(vm_obj const & l) {
    std::ostringstream out;
    out << to_level(l);
    return to_obj(out.str());
}

vm_obj level_fold(vm_obj const &, vm_obj const & l, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    for_each(to_level(l), [&](level const & o) {
            r = invoke(fn, to_obj(o), r);
            return true;
        });
    return r;
}

// meta_constant level.instantiate : level → list (name × level) → list level
vm_obj level_instantiate(vm_obj const & o, vm_obj const & lst) {
    level const & l = to_level(o);
    buffer<name> ns;
    buffer<level> ls;
    vm_obj it = lst;
    while (!is_simple(it)) {
        vm_obj const & h = cfield(it, 0);
        ns.push_back(to_name(cfield(h, 0)));
        ls.push_back(to_level(cfield(h, 1)));
        it = cfield(it, 1);
    }
    return to_obj(instantiate(l, to_list(ns), to_list(ls)));
}

void initialize_vm_level() {
    DECLARE_VM_BUILTIN(name({"level", "zero"}),             level_zero);
    DECLARE_VM_BUILTIN(name({"level", "succ"}),             level_succ);
    DECLARE_VM_BUILTIN(name({"level", "max"}),              level_max);
    DECLARE_VM_BUILTIN(name({"level", "imax"}),             level_imax);
    DECLARE_VM_BUILTIN(name({"level", "param"}),            level_param);
    DECLARE_VM_BUILTIN(name({"level", "global"}),           level_global);
    DECLARE_VM_BUILTIN(name({"level", "mvar"}),             level_mvar);
    DECLARE_VM_BUILTIN(name({"level", "has_decidable_eq"}), level_has_decidable_eq);
    DECLARE_VM_BUILTIN(name({"level", "lt"}),               level_lt);
    DECLARE_VM_BUILTIN(name({"level", "lex_lt"}),           level_lex_lt);
    DECLARE_VM_BUILTIN(name({"level", "eqv"}),              level_eqv);
    DECLARE_VM_BUILTIN(name({"level", "normalize"}),        level_normalize);
    DECLARE_VM_BUILTIN(name({"level", "occurs"}),           level_occurs);
    DECLARE_VM_BUILTIN(name({"level", "to_format"}),        level_to_format);
    DECLARE_VM_BUILTIN(name({"level", "to_string"}),        level_to_string);
    DECLARE_VM_BUILTIN(name({"level", "fold"}),             level_fold);
    DECLARE_VM_BUILTIN(name({"level", "instantiate"}),      level_instantiate);
    DECLARE_VM_CASES_BUILTIN(name({"level", "cases_on"}),   level_cases_on);
}

void finalize_vm_level() {
}
}
