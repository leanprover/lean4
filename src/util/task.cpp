/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/task.h"

namespace lean {

gtask mk_gtask(std::unique_ptr<gtask_imp> && imp, task_flags flags) {
    flags.m_needs_execution = false;
    return std::make_shared<gtask_cell>(gtask_cell::called_from_friend(), imp.release(), flags);
}

void gtask_cell::cancel(std::shared_ptr<cancellable> const & self) {
    if (auto self_task = std::dynamic_pointer_cast<gtask_cell>(self)) {
        taskq().fail_and_dispose(self_task);
    }
}

void task_queue::wait_for_success(gtask const & t) {
    while (true) {
        switch (t->m_state.load()) {
            case task_state::Success:
                return; // OK
            case task_state::Failed:
                std::rethrow_exception(t->m_exception);
            default:
                wait_for_finish(t);
        }
    }
}

void task_queue::execute(gtask const & t) {
    lean_assert(t);
    lean_assert(t->m_state.load() == task_state::Running);
    lean_assert(t->m_data);
    lean_assert(t->m_data->m_imp);

    try {
        {
            buffer<gtask> deps;
            t->m_data->m_imp->get_dependencies(deps);
            if (t->m_data->m_flags.m_propagate_errors_from_dependencies) {
                for (auto & dep : deps) if (dep) wait_for_success(dep);
            } else {
                for (auto & dep : deps) if (dep) wait_for_finish(dep);
            }
        }

        t->execute();
        t->m_state = task_state::Success;
    } catch (...) {
        t->m_exception = std::current_exception();
        t->m_state = task_state::Failed;
    }
}

void task_queue::fail(gtask const & t, std::exception_ptr const & ex) {
    lean_assert(t->m_state.load() < task_state::Running);

    t->m_exception = ex;
    t->m_state = task_state::Failed;
}

void task_queue::fail(gtask const & t, gtask const & failed) {
    lean_assert(failed->m_state.load() == task_state::Failed);

    fail(t, failed->m_exception);
}

static task_queue * g_taskq = nullptr;

void set_task_queue(task_queue * q) {
    if (g_taskq) throw exception("cannot set task queue twice");
    g_taskq = q;
}

task_queue & taskq() {
    return *g_taskq;
}

}
