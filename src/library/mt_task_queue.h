/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <deque>
#include <vector>
#include <unordered_set>
#include <map>
#include <functional>
#include "util/task.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)

class mt_task_queue : public task_queue {
    mutex m_mutex;
    std::map<unsigned, std::deque<gtask>> m_queue;
    std::unordered_set<gtask> m_waiting;
    condition_variable m_queue_added, m_queue_changed;
    void notify_queue_changed();

    bool m_shutting_down = false;
    condition_variable m_shut_down_cv;

    struct worker_info {
        std::unique_ptr<lthread> m_thread;
        gtask m_current_task;
    };
    std::vector<std::shared_ptr<worker_info>> m_workers;
    void spawn_worker();

    unsigned m_sleeping_workers = 0;
    int m_required_workers;
    condition_variable m_wake_up_worker;

    gtask dequeue();
    void enqueue(gtask const &);

    bool check_deps(gtask const &);
    void submit_core(gtask const &, unsigned);
    void bump_prio(gtask const &, unsigned);
    void cancel_core(gtask const &);
    bool empty_core();

    void handle_finished(gtask const &);

    struct mt_sched_info : public scheduling_info {
        unsigned m_prio;
        std::vector<gtask> m_reverse_deps;
        std::shared_ptr<condition_variable> m_has_finished;

        mt_sched_info(unsigned prio) : m_prio(prio) {}

        template <class Fn> void wait(unique_lock<mutex> &, Fn &&);
        void notify();
    };
    mt_sched_info & get_sched_info(gtask const & t) {
        return static_cast<mt_sched_info &>(*get_data(t)->m_sched_info);
    }

    unsigned & get_prio(gtask const & t) { return get_sched_info(t).m_prio; }
    gtask_imp * get_imp(gtask const & t) { return get_data(t)->m_imp.get(); }

    unsigned get_default_prio();

public:
    mt_task_queue(unsigned num_workers);
    ~mt_task_queue();

    void wait_for_finish(gtask const & t) override;
    void fail_and_dispose(gtask const &t) override;

    void submit(gtask const & t, unsigned prio) override;
    void submit(gtask const & t) override;

    void evacuate() override;

    void join() override;
};

#endif

}
