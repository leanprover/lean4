/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/vm/vm_task.h"
#include <string>
#include <iostream>
#include <vector>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_expr.h"
#include "util/task_queue.h"

namespace lean {

template <class A, class B, class Fn>
class map_task : public task<B> {
    Fn m_fn;
    task_result<A> m_in;

public:
    map_task(Fn const & fn, task_result<A> const & in) :
            m_fn(fn), m_in(in) {}

    void description(std::ostream & out) const override {
        out << "mapping";
    }

    bool is_tiny() const override { return true; }

    std::vector<generic_task_result> get_dependencies() override {
        return {m_in};
    }

    B execute() override {
        return m_fn(m_in.get());
    }
};

template <class B, class A, class Fn>
static task_result<B> mk_map_task(task_result<A> const & in, Fn const & fn) {
    return get_global_task_queue()->mk_lazy_task<map_task<A, B, Fn>>(fn, in);
};

struct vm_task : public vm_external {
    task_result<vm_obj> m_val;
    vm_task(task_result<vm_obj> const & v) : m_val(v) {}
    virtual ~vm_task() {}
    virtual void dealloc() override { this->~vm_task(); get_vm_allocator().deallocate(sizeof(vm_task), this); }
};

bool is_task(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_task *>(to_external(o));
}

task_result<vm_obj> & to_task(vm_obj const & o) {
    lean_assert(is_task(o));
    return static_cast<vm_task*>(to_external(o))->m_val;
}

vm_obj to_obj(task_result<vm_obj> const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_task))) vm_task(n));
}

vm_obj to_obj(task_result<expr> const & n) {
    return to_obj(mk_map_task<vm_obj>(n, [] (expr const & e) { return to_obj(e); }));
}

task_result<expr> to_expr_task(vm_obj const & o) {
    return mk_map_task<expr>(to_task(o), [] (vm_obj const & o) { return to_expr(o); });
}

vm_obj vm_task_get(vm_obj const &, vm_obj const & t) {
    return to_task(t).get();
}

vm_obj vm_task_pure(vm_obj const &, vm_obj const & t) {
    return to_obj(mk_pure_task_result(t, "task.pure"));
}

void initialize_vm_task() {
    DECLARE_VM_BUILTIN(name({"task", "get"}),  vm_task_get);
    DECLARE_VM_BUILTIN(name({"task", "pure"}), vm_task_pure);
}

void finalize_vm_task() {
}

}
