/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/rb_map.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/cmp_result.h"

namespace lean {
struct vm_obj_cmp {
    vm_obj m_cmp;
    int operator()(vm_obj const & o1, vm_obj const & o2) const {
        return cmp_result_to_int(invoke(m_cmp, o1, o2));
    }
    vm_obj_cmp() {}
    explicit vm_obj_cmp(vm_obj const & cmp):m_cmp(cmp) {}
};

typedef rb_map<vm_obj, vm_obj, vm_obj_cmp> vm_obj_map;

struct vm_rb_map : public vm_external {
    vm_obj_map m_map;
    vm_rb_map(vm_obj_map const & m):m_map(m) {}
    virtual ~vm_rb_map() {}
};

vm_obj_map const & to_map(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_rb_map*>(to_external(o)));
    return static_cast<vm_rb_map*>(to_external(o))->m_map;
}

vm_obj to_obj(vm_rb_map const & n) {
    return mk_vm_external(new vm_rb_map(n));
}

vm_obj rb_map_mk(vm_obj const &, vm_obj const &, vm_obj const & cmp) {
    return to_obj(vm_obj_map(vm_obj_cmp(cmp)));
}

vm_obj rb_map_size(vm_obj const &, vm_obj const &, vm_obj const & m) {
    return mk_vm_nat(to_map(m).size());
}

vm_obj rb_map_insert(vm_obj const &, vm_obj const &, vm_obj const & m, vm_obj const & k, vm_obj const & d) {
    return to_obj(insert(to_map(m), k, d));
}

vm_obj rb_map_erase(vm_obj const &, vm_obj const &, vm_obj const & m, vm_obj const & k) {
    return to_obj(erase(to_map(m), k));
}

vm_obj rb_map_contains(vm_obj const &, vm_obj const &, vm_obj const & m, vm_obj const & k) {
    return mk_vm_bool(to_map(m).contains(k));
}

vm_obj rb_map_find(vm_obj const &, vm_obj const &, vm_obj const & m, vm_obj const & k) {
    if (auto d = to_map(m).find(k))
        return mk_vm_some(*d);
    else
        return mk_vm_none();
}

vm_obj rb_map_min(vm_obj const &, vm_obj const &, vm_obj const & m) {
    if (to_map(m).empty())
        return mk_vm_none();
    else
        return mk_vm_some(to_map(m).min());
}

vm_obj rb_map_max(vm_obj const &, vm_obj const &, vm_obj const & m) {
    if (to_map(m).empty())
        return mk_vm_none();
    else
        return mk_vm_some(to_map(m).max());
}

/*
meta_constant fold {key : Type} {data : Type} {A :Type} : rb_map key data → A → (key → data → A → A) → A
*/

void initialize_vm_rb_map() {
    DECLARE_VM_BUILTIN(name({"rb_map", "mk"}),             rb_map_mk);
    DECLARE_VM_BUILTIN(name({"rb_map", "size"}),           rb_map_size);
    DECLARE_VM_BUILTIN(name({"rb_map", "insert"}),         rb_map_insert);
    DECLARE_VM_BUILTIN(name({"rb_map", "erase"}),          rb_map_erase);
    DECLARE_VM_BUILTIN(name({"rb_map", "contains"}),       rb_map_contains);
    DECLARE_VM_BUILTIN(name({"rb_map", "find"}),           rb_map_find);
    DECLARE_VM_BUILTIN(name({"rb_map", "min"}),            rb_map_min);
    DECLARE_VM_BUILTIN(name({"rb_map", "max"}),            rb_map_max);
}

void finalize_vm_rb_map() {
}
}
