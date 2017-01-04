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
#include "util/optional.h"
#include "library/io_state.h"
#include "util/task_queue.h"
#include "library/message_buffer.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)

using mt_tq_prioritizer = std::function<task_priority(generic_task *)>; // NOLINT
// disabling lint because it thinks that this is a cast ^^^

struct mt_tq_status {
    std::vector<generic_task const *> m_executing, m_queued, m_waiting, m_delayed;

    size_t size() const { return m_executing.size() + m_queued.size() + m_waiting.size() + m_delayed.size(); }
    template <class F> void for_each(F && f) const {
        for (auto & t : m_executing) f(t);
        for (auto & t : m_queued) f(t);
        for (auto & t : m_waiting) f(t);
        for (auto & t : m_delayed) f(t);
    }
};
using mt_tq_status_cb = std::function<void(mt_tq_status const &)>;

class mt_task_queue : public task_queue {
    mutex m_mutex;
    std::map<unsigned, std::deque<generic_task_result>> m_queue;
    std::unordered_set<generic_task_result, generic_task_result::hash> m_waiting;
    condition_variable m_queue_added, m_queue_changed;
    void notify_queue_changed();

    bool m_shutting_down = false;
    condition_variable m_shut_down_cv;

    struct worker_info {
        std::unique_ptr<lthread> m_thread;
        generic_task_result m_current_task;
        atomic_bool * m_interrupt_flag = nullptr;
    };
    std::vector<std::shared_ptr<worker_info>> m_workers;
    void spawn_worker();

    unsigned m_sleeping_workers = 0;
    int m_required_workers;
    condition_variable m_wake_up_worker;

    mt_tq_prioritizer m_prioritizer;

    chrono::milliseconds m_monitor_ival = chrono::milliseconds(100);
    progress_cb      m_progress_cb;
    mt_tq_status_cb  m_status_cb;
    std::unique_ptr<lthread> m_monitor_thr;
    bool             m_monitor_needs_to_run = false;

    io_state m_ios;
    message_buffer * m_msg_buf;

    bool empty_core();

    generic_task_result dequeue();
    void enqueue(generic_task_result const &);

    void prepare_task(generic_task_result const &result) override;

    bool check_deps(generic_task_result const &);
    void propagate_failure(generic_task_result const &);
    void submit_core(generic_task_result const &);
    void bump_prio(generic_task_result const &, task_priority const &);
    void cancel_core(generic_task_result const &);

    void reprioritize_core();

    task_priority & get_prio(generic_task_result const & tr) { return get_data(tr).m_prio; }

public:
    mt_task_queue(unsigned num_workers);
    mt_task_queue(unsigned num_workers, mt_tq_prioritizer const & prioritizer);
    ~mt_task_queue();

    optional<generic_task_result> get_current_task() override;
    void join() override;
    bool empty() override;

    void submit(generic_task_result const &) override;
    void wait(generic_task_result const & t) override;
    void cancel(generic_task_result const & t) override;

    void cancel_if(std::function<bool(generic_task *)> const & pred) override; // NOLINT

    void set_monitor_interval(chrono::milliseconds const &);
    void set_progress_callback(progress_cb const & cb) override;
    void set_status_callback(mt_tq_status_cb const & cb);

    void reprioritize(mt_tq_prioritizer const & p);
    void reprioritize();
};
#endif

}
