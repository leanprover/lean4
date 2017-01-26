/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"

namespace lean {
template<typename A>
struct vm_list : public vm_external {
    list<A> m_val;
    vm_list(list<A> const & v):m_val(v) {}
    virtual ~vm_list() {}
    virtual void dealloc() override {
        this->~vm_list(); get_vm_allocator().deallocate(sizeof(vm_list<A>), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_list<A>(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_list<A>))) vm_list<A>(m_val); }
};

template<typename A>
vm_obj list_to_obj(list<A> const & l) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_list<A>))) vm_list<A>(l));
}

vm_obj to_obj(list<name> const & ls) { return list_to_obj(ls); }
vm_obj to_obj(list<level> const & ls) { return list_to_obj(ls); }
vm_obj to_obj(list<expr> const & ls) { return list_to_obj(ls); }

vm_obj to_obj(buffer<name> const & ls) { return to_obj(to_list(ls)); }
vm_obj to_obj(buffer<level> const & ls) { return to_obj(to_list(ls)); }
vm_obj to_obj(buffer<expr> const & ls) { return to_obj(to_list(ls)); }

#define MK_TO_LIST(A, ToA)                                              \
list<A> to_list_ ## A(vm_obj const & o) {                               \
    if (is_simple(o)) {                                                 \
        return list<A>();                                               \
    } else if (is_constructor(o)) {                                     \
        return list<A>(ToA(cfield(o, 0)), to_list_ ## A(cfield(o, 1))); \
    } else {                                                            \
        lean_assert(is_external(o));                                    \
        lean_assert(dynamic_cast<vm_list<A>*>(to_external(o)));         \
        return static_cast<vm_list<A>*>(to_external(o))->m_val;         \
    }                                                                   \
}

MK_TO_LIST(name, to_name)
MK_TO_LIST(level, to_level)
MK_TO_LIST(expr, to_expr)

#define MK_TO_BUFFER(A, ToA)                                            \
void to_buffer_ ## A(vm_obj const & o, buffer<A> & r) {                 \
    if (is_simple(o)) {                                                 \
        return;                                                         \
    } else if (is_constructor(o)) {                                     \
        r.push_back(ToA(cfield(o, 0)));                                 \
        to_buffer_ ## A(cfield(o, 1), r);                               \
    } else {                                                            \
        lean_assert(is_external(o));                                    \
        lean_assert(dynamic_cast<vm_list<A>*>(to_external(o)));         \
        to_buffer(static_cast<vm_list<A>*>(to_external(o))->m_val, r);  \
    }                                                                   \
}

MK_TO_BUFFER(name, to_name)
MK_TO_BUFFER(level, to_level)
MK_TO_BUFFER(expr, to_expr)

template<typename A>
unsigned list_cases_on_core(list<A> const & l, buffer<vm_obj> & data) {
    if (empty(l)) {
        return 0;
    } else  {
        data.push_back(to_obj(head(l)));
        data.push_back(list_to_obj(tail(l)));
        return 1;
    }
}

unsigned list_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    if (is_simple(o)) {
        return 0;
    } else if (is_constructor(o)) {
        data.append(csize(o), cfields(o));
        return 1;
    } else {
        lean_assert(is_external(o));
        if (auto l = dynamic_cast<vm_list<name>*>(to_external(o))) {
            return list_cases_on_core(l->m_val, data);
        } else if (auto l = dynamic_cast<vm_list<expr>*>(to_external(o))) {
            return list_cases_on_core(l->m_val, data);
        } else if (auto l = dynamic_cast<vm_list<level>*>(to_external(o))) {
            return list_cases_on_core(l->m_val, data);
        } else {
            lean_unreachable();
        }
    }
}

vm_obj to_obj(list<unsigned> const & ls) {
    return to_vm_list(ls, [&](unsigned n) { return mk_vm_nat(n); });
}

void initialize_vm_list() {
    DECLARE_VM_CASES_BUILTIN(name({"list", "cases_on"}), list_cases_on);
}

void finalize_vm_list() {
}
}
