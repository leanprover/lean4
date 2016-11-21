/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "util/task_queue.h"

namespace lean {

std::string generic_task::description() const {
    std::ostringstream out;
    description(out);
    return out.str();
}

void generic_task::set_result(generic_task_result const &) {}

generic_task_result_cell::generic_task_result_cell(generic_task * t) :
        m_rc(0), m_task(t), m_desc(t->description()) {}

void generic_task_result_cell::clear_task() {
    if (m_task) {
        delete m_task;
        m_task = nullptr;
    }
}

bool generic_task_result_cell::execute() {
    lean_assert(!has_evaluated());
    try {
        execute_and_store_result();
        return true;
    } catch (interrupted) {
        m_ex = std::make_exception_ptr(
                task_cancellation_exception(generic_task_result(this)));
        return false;
    } catch (...) {
        m_ex = std::current_exception();
        return false;
    }
}

LEAN_THREAD_PTR(task_queue, g_tq);
scope_global_task_queue::scope_global_task_queue(task_queue * tq) {
    m_old_tq = g_tq;
    g_tq = tq;
}
scope_global_task_queue::~scope_global_task_queue() {
    g_tq = m_old_tq;
}
task_queue & get_global_task_queue() {
    return *g_tq;
}

task_cancellation_exception::task_cancellation_exception(generic_task_result const & cancelled_task) :
        m_cancelled_task(cancelled_task) {
    std::ostringstream out;
    if (cancelled_task) {
        out << "task cancelled: " << cancelled_task.description();
    } else {
        out << "task cancelled";
    }
    m_msg = out.str();
}

char const *task_cancellation_exception::what() const noexcept {
    return m_msg.c_str();
}

}
