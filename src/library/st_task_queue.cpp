/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <vector>
#include "library/st_task_queue.h"
#include "task_helper.h"
#include "library/message_buffer.h"

namespace lean {

st_task_queue::st_task_queue() {}

void st_task_queue::wait(generic_task_result const & t) {
    if (unwrap(t)->m_state.load() != task_result_state::FINISHED)
        std::rethrow_exception(unwrap(t)->m_ex);
}

void st_task_queue::join() {}

bool st_task_queue::empty() {
    return true;
}

optional<generic_task_result> st_task_queue::get_current_task() {
    return optional<generic_task_result>();
}

void st_task_queue::submit(generic_task_result const & t) {
    set_bucket(t, get_scope_message_context().new_sub_bucket());

    std::vector<generic_task_result> deps;
    try { deps = unwrap(t)->m_task->get_dependencies(); } catch (...) {}
    for (auto & d : deps) {
        switch (unwrap(d)->m_state.load()) {
            case task_result_state::FAILED:
                unwrap(t)->m_state = task_result_state::FAILED;
                unwrap(t)->m_ex = unwrap(d)->m_ex;
                unwrap(t)->clear_task();
                return;
            case task_result_state::FINISHED:
                break;
            default:
                lean_unreachable();
        }
    }

    if (m_progress_cb) m_progress_cb(unwrap(t)->m_task);
    bool is_ok = execute_task_with_scopes(unwrap(t));
    unwrap(t)->m_state = is_ok ? task_result_state::FINISHED : task_result_state::FAILED;
    unwrap(t)->clear_task();
}

void st_task_queue::cancel(generic_task_result const &) {}

void st_task_queue::set_progress_callback(progress_cb const & cb) {
    m_progress_cb = cb;
}

void st_task_queue::cancel_if(const std::function<bool(generic_task *)> &) {} // NOLINT

}
