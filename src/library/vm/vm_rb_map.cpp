/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <iostream>
#include "util/rb_map.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_ordering.h"

namespace lean {
struct vm_obj_cmp {
    vm_obj m_cmp;
    int operator()(vm_obj const & o1, vm_obj const & o2) const {
        return ordering_to_int(invoke(m_cmp, o1, o2));
    }
    vm_obj_cmp() {}
    explicit vm_obj_cmp(vm_obj const & cmp):m_cmp(cmp) {}
};

typedef rb_map<vm_obj, vm_obj, vm_obj_cmp> vm_obj_map;

struct vm_rb_map : public vm_external {
    vm_obj_map m_map;
    vm_rb_map(vm_obj_map const & m):m_map(m) {}
    virtual ~vm_rb_map() {}
    virtual void dealloc() override { this->~vm_rb_map(); get_vm_allocator().deallocate(sizeof(vm_rb_map), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override;
    virtual vm_external * clone(vm_clone_fn const &) override { lean_unreachable(); }
};

/* Auxiliary object used by vm_rb_map::ts_clone.
   This is the "thread safe" version used when creating a ts_vm_obj that contains
   a nested vm_rb_map. */
struct vm_rb_map_ts_copy : public vm_external {
    vm_obj                            m_cmp;
    std::vector<pair<vm_obj, vm_obj>> m_entries;
    virtual ~vm_rb_map_ts_copy() {
        /* The object ts_vm_obj manages the life cycle of all vm_obj's.
           We should prevent this destructor from invoking the destructor of m_cmp and the
           vm_obj's nested in m_entries. */
        m_cmp.steal_ptr();
        for (auto & p : m_entries) {
            if (p.first.is_ptr())
                p.first.steal_ptr();
            if (p.second.is_ptr())
                p.second.steal_ptr();
        }
    }
    virtual void dealloc() override { lean_unreachable(); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
    virtual vm_external * clone(vm_clone_fn const &) override;
};

vm_external * vm_rb_map::ts_clone(vm_clone_fn const & fn) {
    vm_rb_map_ts_copy * r = new vm_rb_map_ts_copy();
    r->m_cmp = fn(m_map.get_cmp().m_cmp);
    m_map.for_each([&](vm_obj const & k, vm_obj const & v) {
            r->m_entries.emplace_back(fn(k), fn(v));
        });
    return r;
}

vm_external * vm_rb_map_ts_copy::clone(vm_clone_fn const & fn) {
    vm_obj new_cmp = fn(m_cmp);
    vm_obj_map new_map = vm_obj_map(vm_obj_cmp(new_cmp));
    for (auto const & p : m_entries) {
        new_map.insert(fn(p.first), fn(p.second));
    }
    return new (get_vm_allocator().allocate(sizeof(vm_rb_map))) vm_rb_map(new_map);
}

vm_obj_map const & to_map(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_rb_map*>(to_external(o)));
    return static_cast<vm_rb_map*>(to_external(o))->m_map;
}

vm_obj to_obj(vm_rb_map const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_rb_map))) vm_rb_map(n));
}

vm_obj rb_map_mk_core(vm_obj const &, vm_obj const &, vm_obj const & cmp) {
    return to_obj(vm_obj_map(vm_obj_cmp(cmp)));
}

vm_obj rb_map_size(vm_obj const &, vm_obj const &, vm_obj const & m) {
    return mk_vm_nat(to_map(m).size());
}

vm_obj rb_map_empty(vm_obj const &, vm_obj const &, vm_obj const & m) {
    return mk_vm_bool(to_map(m).empty());
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

vm_obj rb_map_fold(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const & m, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    to_map(m).for_each([&](vm_obj const & k, vm_obj const & d) {
            r = invoke(fn, k, d, r);
        });
    return r;
}

struct vm_name_set : public vm_external {
    name_set m_val;
    vm_name_set(name_set const & v):m_val(v) {}
    virtual ~vm_name_set() {}
    virtual void dealloc() override { this->~vm_name_set(); get_vm_allocator().deallocate(sizeof(vm_name_set), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_name_set(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_name_set))) vm_name_set(m_val); }
};

bool is_name_set(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_name_set*>(to_external(o));
}

name_set const & to_name_set(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_name_set*>(to_external(o)));
    return static_cast<vm_name_set*>(to_external(o))->m_val;
}

vm_obj to_obj(name_set const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_name_set))) vm_name_set(n));
}

vm_obj mk_name_set() {
    return to_obj(name_set());
}

vm_obj name_set_size(vm_obj const & m) {
    return mk_vm_nat(to_name_set(m).size());
}

vm_obj name_set_empty(vm_obj const & m) {
    return mk_vm_bool(to_name_set(m).empty());
}

vm_obj name_set_insert(vm_obj const & m, vm_obj const & k) {
    return to_obj(insert(to_name_set(m), to_name(k)));
}

vm_obj name_set_erase(vm_obj const & m, vm_obj const & k) {
    return to_obj(erase(to_name_set(m), to_name(k)));
}

vm_obj name_set_contains(vm_obj const & m, vm_obj const & k) {
    return mk_vm_bool(to_name_set(m).contains(to_name(k)));
}

vm_obj name_set_fold(vm_obj const &, vm_obj const & m, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    to_name_set(m).for_each([&](name const & k) {
            r = invoke(fn, to_obj(k), r);
        });
    return r;
}

void initialize_vm_rb_map() {
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "mk_core"}),        rb_map_mk_core);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "size"}),           rb_map_size);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "empty"}),          rb_map_empty);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "insert"}),         rb_map_insert);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "erase"}),          rb_map_erase);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "contains"}),       rb_map_contains);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "find"}),           rb_map_find);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "min"}),            rb_map_min);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "max"}),            rb_map_max);
    DECLARE_VM_BUILTIN(name({"native", "rb_map", "fold"}),           rb_map_fold);

    DECLARE_VM_BUILTIN(name({"mk_name_set"}),              mk_name_set);
    DECLARE_VM_BUILTIN(name({"name_set", "size"}),         name_set_size);
    DECLARE_VM_BUILTIN(name({"name_set", "empty"}),        name_set_empty);
    DECLARE_VM_BUILTIN(name({"name_set", "insert"}),       name_set_insert);
    DECLARE_VM_BUILTIN(name({"name_set", "erase"}),        name_set_erase);
    DECLARE_VM_BUILTIN(name({"name_set", "contains"}),     name_set_contains);
    DECLARE_VM_BUILTIN(name({"name_set", "fold"}),         name_set_fold);
}

void finalize_vm_rb_map() {
}
}
