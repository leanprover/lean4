/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <deque>
#include <string>
#include <vector>
#include <unordered_set>
#include <map>
#include <functional>
#include <unordered_map>
#include <library/io_state.h>
#include "util/optional.h"
#include "library/task_queue.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)

using mt_tq_prioritizer = std::function<task_priority(generic_task *)>; // NOLINT
// disabling lint because it thinks that this is a cast ^^^

class mt_task_queue : public task_queue {
    mutex m_mutex;
    std::map<unsigned, std::deque<generic_task_result>> m_queue;
    std::unordered_set<generic_task_result, generic_task_result::hash> m_waiting;
    condition_variable m_queue_added, m_queue_removed;

    struct worker_info {
        thread m_thread;
        generic_task_result m_current_task;
        atomic_bool * m_interrupt_flag = nullptr;
    };
    std::vector<std::shared_ptr<worker_info>> m_workers;
    bool m_shutting_down = false;
    void spawn_worker();

    unsigned m_sleeping_workers = 0;
    int m_required_workers;
    condition_variable m_wake_up_worker;

    mt_tq_prioritizer m_prioritizer;
    progress_cb m_progress_cb;

    io_state m_ios;
    message_buffer * m_msg_buf;

    generic_task_result dequeue();
    void enqueue(generic_task_result const &);

    bool check_deps(generic_task_result const &);
    void propagate_failure(generic_task_result const &);
    void submit(generic_task_result const &) override;
    void bump_prio(generic_task_result const &, task_priority const &);
    void cancel_core(generic_task_result const &);

    void reprioritize_core();

public:
    mt_task_queue(unsigned num_workers);
    mt_task_queue(unsigned num_workers, mt_tq_prioritizer const & prioritizer);
    ~mt_task_queue();

    optional<generic_task_result> get_current_task() override;
    bool empty() override;

    void wait(generic_task_result const & t) override;
    void cancel(generic_task_result const & t) override;

    void cancel_if(std::function<bool(generic_task *)> const & pred) override; // NOLINT

    void set_progress_callback(progress_cb const & cb) override;

    void reprioritize(mt_tq_prioritizer const & p);
    void reprioritize();
};
#endif

}
