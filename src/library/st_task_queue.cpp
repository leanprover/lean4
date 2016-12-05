/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/st_task_queue.h"

namespace lean {

st_task_queue::st_task_queue() {}

void st_task_queue::wait(generic_task_result const & t) {
    if (t->m_state.load() != task_result_state::FINISHED)
        std::rethrow_exception(t->m_ex);
}

void st_task_queue::join() {}

bool st_task_queue::empty() {
    return true;
}

optional<generic_task_result> st_task_queue::get_current_task() {
    return optional<generic_task_result>();
}

void st_task_queue::submit(generic_task_result const & t) {
    if (m_progress_cb) m_progress_cb(t->m_task);
    bool is_ok = t->execute();
    t->m_state = is_ok ? task_result_state::FINISHED : task_result_state::FAILED;
    t->clear_task();
}

void st_task_queue::cancel(generic_task_result const &) {}

void st_task_queue::set_progress_callback(progress_cb const & cb) {
    m_progress_cb = cb;
}

void st_task_queue::cancel_if(const std::function<bool(generic_task *)> &) {} // NOLINT

}
