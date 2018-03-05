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
#include "library/library_task_builder.h"

namespace lean {

struct vm_task : public vm_external {
    task<ts_vm_obj> m_val;
    vm_task(task<ts_vm_obj> const & v) : m_val(v) {}
    virtual ~vm_task() {}
    virtual void dealloc() override { this->~vm_task(); get_vm_allocator().deallocate(sizeof(vm_task), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        return new vm_task(m_val);
    }
    virtual vm_external * clone(vm_clone_fn const &) override {
        lean_unreachable();
    }
};

bool is_task(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_task *>(to_external(o));
}

task<ts_vm_obj> const & to_task(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_task *>(to_external(o)));
    return static_cast<vm_task*>(to_external(o))->m_val;
}

vm_obj to_obj(task<ts_vm_obj> const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_task))) vm_task(n));
}

vm_obj to_obj(task<expr> const & n) {
    return to_obj(map<ts_vm_obj>(n, [] (expr const & e) { return ts_vm_obj(to_obj(e)); }).execute_eagerly().build());
}

task<expr> to_expr_task(vm_obj const & o) {
    return map<expr>(to_task(o), [] (ts_vm_obj const & o) { return to_expr(o.to_vm_obj()); }).execute_eagerly().build();
}

vm_obj vm_task_get(vm_obj const &, vm_obj const & t) {
    return get(to_task(t)).to_vm_obj();
}

vm_obj vm_task_pure(vm_obj const &, vm_obj const & t) {
    return to_obj(mk_pure_task(ts_vm_obj(t)));
}

vm_obj vm_task_map(vm_obj const &, vm_obj const &, vm_obj const & fn, vm_obj const & t) {
    auto env = get_vm_state().env();
    auto opts = get_vm_state().get_options();
    auto has_infom = get_global_info_manager() != nullptr;
    auto ts_fn = ts_vm_obj(fn);
    return to_obj(add_library_task(map<ts_vm_obj>(to_task(t), [env, opts, has_infom, ts_fn] (ts_vm_obj const & arg) {
        auto file_name = logtree().get_location().m_file_name;

        // Tracing
        type_context_old tc(env);
        scope_trace_env scope_trace(env, opts, tc);
        scope_traces_as_messages scope_traces_as_msg(file_name, logtree().get_location().m_range.m_begin);

        // Info manager
        auto_reporting_info_manager_scope scope_infom(file_name, has_infom);

        vm_state state(env, opts);
        scope_vm_state scope_vm(state);
        return ts_vm_obj(state.invoke(ts_fn.to_vm_obj(), arg.to_vm_obj()));
    }).wrap(exception_reporter())));
}

vm_obj vm_task_flatten(vm_obj const &, vm_obj const & o) {
    auto t = to_task(o);
    return to_obj(task_builder<ts_vm_obj>([t] {
        return get(to_task(get(t).to_vm_obj()));
    }).depends_on_fn([t] (buffer<gtask> & deps) {
        deps.push_back(t);
        if (auto res = peek(t))
            deps.push_back(to_task(res->to_vm_obj()));
    }).execute_eagerly().build());
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
