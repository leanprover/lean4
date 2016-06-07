/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/standard_kernel.h"
#include "library/hott_kernel.h"
#include "library/util.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_exceptional.h"


namespace lean {
struct vm_environment : public vm_external {
    environment m_val;
    vm_environment(environment const & v):m_val(v) {}
    virtual void dealloc() override { this->~vm_environment(); get_vm_allocator().deallocate(sizeof(vm_environment), this); }
};

environment const & to_env(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_environment*>(to_external(o)));
    return static_cast<vm_environment*>(to_external(o))->m_val;
}

vm_obj to_obj(environment const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_environment))) vm_environment(n));
}

vm_obj environment_mk_std(vm_obj const & l) {
    return to_obj(mk_environment(force_to_unsigned(l, 0)));
}

vm_obj environment_mk_hott(vm_obj const & l) {
    return to_obj(mk_hott_environment(force_to_unsigned(l, 0)));
}

vm_obj environment_trust_lvl(vm_obj const & env) {
    return mk_vm_nat(to_env(env).trust_lvl());
}

vm_obj environment_is_std(vm_obj const & env) {
    return mk_vm_bool(is_standard(to_env(env)));
}

vm_obj environment_add(vm_obj const & env, vm_obj const & decl) {
    try {
        return mk_vm_exceptional_success(to_obj(to_env(env).add(check(to_env(env), to_declaration(decl)))));
    } catch (throwable & ex) {
        return mk_vm_exceptional_exception(ex);
    }
}

vm_obj environment_get(vm_obj const & env, vm_obj const & n) {
    try {
        return mk_vm_exceptional_success(to_obj(to_env(env).get(to_name(n))));
    } catch (throwable & ex) {
        return mk_vm_exceptional_exception(ex);
    }
}

/*
/- Add a new inductive datatype to the environment
   name, universe parameters, number of parameters, type, constructors (name and type) -/
meta_constant add_inductive   : environment → name → list name → nat → expr → list (name × expr) → exceptional environment
/- Return tt iff the given name is an inductive datatype -/
meta_constant is_inductive    : environment → name → bool
/- Return tt iff the given name is a constructor -/
meta_constant is_constructor  : environment → name → bool
/- Return tt iff the given name is a recursor -/
meta_constant is_recursor     : environment → name → bool
/- Return the constructors of the inductive datatype with the given name -/
meta_constant constructors_of : environment → name → list name
/- Return the recursor of the given inductive datatype -/
meta_constant recursor_of     : environment → name → option name
/- Return the number of parameters of the inductive datatype -/
meta_constant inductive_num_params : environment → name → nat
/- Return the number of indices of the inductive datatype -/
meta_constant inductive_num_indices : environment → name → nat
/- Return tt iff the inductive datatype recursor supports dependent elimination -/
meta_constant inductive_dep_elim : environment → name → bool
/- Fold over declarations in the environment -/
meta_constant fold {A :Type} : environment → A → (declaration → A → A) → A
*/

void initialize_vm_environment() {
    DECLARE_VM_BUILTIN(name({"environment", "mk_std"}),         environment_mk_std);
    DECLARE_VM_BUILTIN(name({"environment", "mk_hott"}),        environment_mk_hott);
    DECLARE_VM_BUILTIN(name({"environment", "trust_lvl"}),      environment_trust_lvl);
    DECLARE_VM_BUILTIN(name({"environment", "is_std"}),         environment_is_std);
    DECLARE_VM_BUILTIN(name({"environment", "add"}),            environment_add);
    DECLARE_VM_BUILTIN(name({"environment", "get"}),            environment_get);
}

void finalize_vm_environment() {
}
}
