/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/vm/vm_task.h"
#include <string>
#include <iostream>
#include <vector>
#include "library/trace.h"
#include "library/type_context.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "library/tactic/elaborate.h"
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
    task_result<ts_vm_obj> m_val;
    vm_task(task_result<ts_vm_obj> const & v) : m_val(v) {}
    virtual ~vm_task() {}
    virtual void dealloc() override { this->~vm_task(); get_vm_allocator().deallocate(sizeof(vm_task), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        /* A possible workaround is to use get() here and wait for the task to be done. */
        throw exception("vm_task object cannot be copied to thread safe storage");
    }
    virtual vm_external * clone(vm_clone_fn const &) override {
        lean_unreachable();
    }
};

bool is_task(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_task *>(to_external(o));
}

task_result<ts_vm_obj> const & to_task(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_task *>(to_external(o)));
    return static_cast<vm_task*>(to_external(o))->m_val;
}

vm_obj to_obj(task_result<ts_vm_obj> const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_task))) vm_task(n));
}

vm_obj to_obj(task_result<expr> const & n) {
    return to_obj(mk_map_task<ts_vm_obj>(n, [] (expr const & e) { return ts_vm_obj(to_obj(e)); }));
}

task_result<expr> to_expr_task(vm_obj const & o) {
    return mk_map_task<expr>(to_task(o), [] (ts_vm_obj const & o) { return to_expr(o.to_vm_obj()); });
}

vm_obj vm_task_get(vm_obj const &, vm_obj const & t) {
    return to_task(t).get().to_vm_obj();
}

vm_obj vm_task_pure(vm_obj const &, vm_obj const & t) {
    return to_obj(mk_pure_task_result(ts_vm_obj(t), "task.pure"));
}

struct vm_map_task : public task<ts_vm_obj> {
    environment m_env;
    options m_opts;
    bool m_use_infom;
    ts_vm_obj m_fn;
    task_result<ts_vm_obj> m_arg;

public:
    vm_map_task(environment const & env, options const & opts, bool use_infom,
                 ts_vm_obj const & fn, task_result<ts_vm_obj> const & arg) :
            m_env(env), m_opts(opts), m_use_infom(use_infom), m_fn(fn), m_arg(arg) {}

    void description(std::ostream & out) const override {
        out << "task.map";
    }

    std::vector<generic_task_result> get_dependencies() override {
        return {m_arg};
    }

    ts_vm_obj execute() override {
        // Tracing
        type_context tc(m_env);
        scope_trace_env scope_trace(m_env, m_opts, tc);

        // Info manager
        auto_reporting_info_manager_scope scope_infom(get_module_id(), m_use_infom);

        vm_state state(m_env, m_opts);
        scope_vm_state scope_vm(state);
        return ts_vm_obj(state.invoke(m_fn.to_vm_obj(), m_arg.get().to_vm_obj()));
    }
};

struct vm_flatten_task : public task<ts_vm_obj> {
    task_result<ts_vm_obj> m_task;

public:
    vm_flatten_task(task_result<ts_vm_obj> const & t) : m_task(t) {}

    void description(std::ostream & out) const override {
        out << "task.flatten";
    }

    bool is_tiny() const override { return true; }

    std::vector<generic_task_result> get_dependencies() override {
        std::vector<generic_task_result> deps = { m_task };
        if (auto res = m_task.peek())
            deps.push_back(to_task(res->to_vm_obj()));
        return deps;
    }

    ts_vm_obj execute() override {
        return to_task(m_task.get().to_vm_obj()).get();
    }
};

vm_obj vm_task_map(vm_obj const &, vm_obj const &, vm_obj const & fn, vm_obj const & t) {
    return to_obj(get_global_task_queue()->submit<vm_map_task>(
            get_vm_state().env(), get_vm_state().get_options(),
            get_global_info_manager() != nullptr,
            ts_vm_obj(fn), to_task(t)));
}

vm_obj vm_task_flatten(vm_obj const &, vm_obj const & t) {
    return to_obj(get_global_task_queue()->submit<vm_flatten_task>(to_task(t)));
}

void initialize_vm_task() {
    DECLARE_VM_BUILTIN(name({"task", "get"}),  vm_task_get);
    DECLARE_VM_BUILTIN(name({"task", "pure"}), vm_task_pure);
    DECLARE_VM_BUILTIN(name({"task", "map"}),  vm_task_map);
    DECLARE_VM_BUILTIN(name({"task", "flatten"}), vm_task_flatten);
}

void finalize_vm_task() {
}

}
