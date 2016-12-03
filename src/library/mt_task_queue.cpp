/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <algorithm>
#include <vector>
#include "library/mt_task_queue.h"
#include "util/interrupt.h"
#include "util/flet.h"

#if defined(LEAN_MULTI_THREAD)
namespace lean {

LEAN_THREAD_PTR(generic_task_result, g_current_task);
struct scoped_current_task {
    generic_task_result * m_old;
    scoped_current_task(generic_task_result * t) :
            m_old(g_current_task) {
        g_current_task = t;
    }
    ~scoped_current_task() {
        g_current_task = m_old;
    }
};

template <class T>
struct scoped_add {
    T & m_ref;
    T m_delta;
    scoped_add(T & ref, T delta) : m_ref(ref), m_delta(delta) {
        m_ref += m_delta;
    }
    ~scoped_add() {
        m_ref -= m_delta;
    }
};

mt_task_queue::mt_task_queue(unsigned num_workers) :
    mt_task_queue(num_workers, [=] (generic_task *) { // NOLINT
        task_priority p;
        p.m_prio = 0;
        return p;
    }) {}

mt_task_queue::mt_task_queue(unsigned num_workers, mt_tq_prioritizer const & prioritizer) :
        m_required_workers(num_workers), m_prioritizer(prioritizer),
        m_ios(get_global_ios()), m_msg_buf(&get_global_message_buffer()) {
    for (unsigned i = 0; i < num_workers; i++)
        spawn_worker();
}

mt_task_queue::~mt_task_queue() {
    {
        unique_lock<mutex> lock(m_mutex);
        m_queue_removed.wait(lock, [=] { return empty_core(); });
        m_shutting_down = true;
        m_queue_added.notify_all();
        m_wake_up_worker.notify_all();
    }
    for (auto & w : m_workers) w->m_thread.join();
}

void mt_task_queue::spawn_worker() {
    lean_assert(!m_shutting_down);
    auto this_worker = std::make_shared<worker_info>();
    this_worker->m_thread = thread([=] {
        save_stack_info(false);
        this_worker->m_interrupt_flag = get_interrupt_flag();

        scope_global_task_queue scope_tq(this);
        scope_global_ios scope_ios(m_ios);
        scoped_message_buffer scope_msg_buf(m_msg_buf);

        unique_lock<mutex> lock(m_mutex);
        scoped_add<int> dec_required(m_required_workers, -1);
        while (true) {
            if (m_shutting_down) {
                run_thread_finalizers();
                run_post_thread_finalizers();
                return;
            }
            if (m_required_workers < 0) {
                scoped_add<int> inc_required(m_required_workers, +1);
                scoped_add<unsigned> inc_sleeping(m_sleeping_workers, +1);
                m_wake_up_worker.wait(lock);
                continue;
            }
            if (m_queue.empty()) {
                m_queue_added.wait(lock);
                continue;
            }

            auto t = dequeue();
            if (t->m_state.load() != task_result_state::QUEUED) continue;

            t->m_state = task_result_state::EXECUTING;
            bool is_ok;
            auto cb = m_progress_cb;
            reset_interrupt();
            {
                flet<generic_task_result> _(this_worker->m_current_task, t);
                scoped_current_task scope_cur_task(&t);
                lock.unlock();
                if (cb) cb(t->m_task);
                is_ok = t->execute();
                lock.lock();
            }
            reset_interrupt();

            t->m_state = is_ok ? task_result_state::FINISHED : task_result_state::FAILED;
            t->m_task->m_has_finished.notify_all();

            if (is_ok) {
                for (auto & rdep : t->m_task->m_reverse_deps) {
                    if (rdep->has_evaluated()) {
                        m_waiting.erase(rdep);
                    } else {
                        switch (rdep->m_state.load()) {
                            case task_result_state::WAITING:
                                if (check_deps(rdep)) {
                                    m_waiting.erase(rdep);
                                    if (!rdep->has_evaluated())
                                        enqueue(rdep);
                                }
                                break;
                            case task_result_state::QUEUED: break;
                            case task_result_state::FAILED: break;
                            default:
                                lean_unreachable();
                        }
                    }
                }
            } else {
                propagate_failure(t);
            }

            t->clear_task();
            m_queue_removed.notify_all();
        }
    });
    m_workers.push_back(this_worker);
}

void mt_task_queue::propagate_failure(generic_task_result const & tr) {
    lean_assert(tr->m_state.load() == task_result_state::FAILED);
    m_waiting.erase(tr);

    if (auto t = tr->m_task) {
        tr->m_task->m_has_finished.notify_all();

        for (auto & rdep : t->m_reverse_deps) {
            switch (rdep->m_state.load()) {
                case task_result_state::WAITING:
                case task_result_state::QUEUED:
                    rdep->m_ex = tr->m_ex;
                    rdep->m_state = task_result_state::FAILED;
                    propagate_failure(rdep);
                    break;
                default: break;
            }
        }
    }

    tr->clear_task();
}

void mt_task_queue::submit(generic_task_result const & t) {
    unique_lock<mutex> lock(m_mutex);
    check_interrupted();
    t->m_task->m_prio = m_prioritizer(t->m_task);
    if (check_deps(t)) {
        if (!t->has_evaluated()) {
            enqueue(t);
        }
    } else {
        t->m_state = task_result_state::WAITING;
        m_waiting.insert(t);
    }
}

void mt_task_queue::bump_prio(generic_task_result const & t, task_priority const & new_prio) {
    if (t->m_task && new_prio < t->m_task->m_prio) {
        switch (t->m_state.load()) {
        case task_result_state::QUEUED: {
            auto prio = t->m_task->m_prio.m_prio;
            auto &q = m_queue[prio];
            auto it = std::find(q.begin(), q.end(), t);
            lean_assert(it != q.end());
            q.erase(it);
            if (q.empty()) m_queue.erase(prio);

            t->m_task->m_prio.bump(new_prio);
            check_deps(t);
            enqueue(t);
            break;
        }
        case task_result_state::WAITING:
            t->m_task->m_prio.bump(new_prio);
            check_deps(t);
            break;
        case task_result_state::EXECUTING:
        case task_result_state::FINISHED:
        case task_result_state::FAILED:
            break;
        default: lean_unreachable();
        }
    }
}

bool mt_task_queue::check_deps(generic_task_result const & t) {
    std::vector<generic_task_result> deps;
    try {
        deps = t->m_task->get_dependencies();
    } catch (...) {}
    for (auto & dep : deps) {
        if (dep) bump_prio(dep, t->m_task->m_prio);
    }
    for (auto & dep : deps) {
        if (!dep) continue;
        switch (dep->m_state.load()) {
            case task_result_state::WAITING:
            case task_result_state::QUEUED:
            case task_result_state::EXECUTING:
                lean_assert(dep->m_task);
                dep->m_task->m_reverse_deps.push_back(t);
                return false;
            case task_result_state::FINISHED:
                break;
            case task_result_state::FAILED:
                t->m_ex = dep->m_ex;
                t->m_state = task_result_state::FAILED;
                propagate_failure(t);
                return true;
            default: lean_unreachable();
        }
    }
    return true;
}

void mt_task_queue::wait(generic_task_result const & t) {
    if (!t) return;
    unique_lock<mutex> lock(m_mutex);
    if (g_current_task && t->m_task && (*g_current_task)->m_task->m_prio < t->m_task->m_prio) {
        bump_prio(t, (*g_current_task)->m_task->m_prio);
    }
    while (!t->has_evaluated()) {
        if (g_current_task) {
            scoped_add<int> inc_required(m_required_workers, +1);
            if (m_sleeping_workers == 0) {
                spawn_worker();
            } else {
                m_wake_up_worker.notify_one();
            }
            t->m_task->m_has_finished.wait(lock);
        } else {
            t->m_task->m_has_finished.wait(lock);
        }
    }
    switch (t->m_state.load()) {
        case task_result_state::FAILED: std::rethrow_exception(t->m_ex);
        case task_result_state::FINISHED: return;
        default: throw exception("invalid task state");
    }
}

void mt_task_queue::cancel_if(const std::function<bool(generic_task *)> & pred) { // NOLINT
    std::vector<generic_task_result> to_cancel;
    unique_lock<mutex> lock(m_mutex);

    for (auto & w : m_workers)
        if (w->m_current_task && pred(w->m_current_task->m_task))
            to_cancel.push_back(w->m_current_task);

    for (auto & q : m_queue)
        for (auto & t : q.second)
            if (t->m_task && pred(t->m_task))
                to_cancel.push_back(t);

    for (auto & t : m_waiting)
        if (t->m_task && pred(t->m_task))
            to_cancel.push_back(t);

    for (auto & t : to_cancel)
        cancel_core(t);
}

void mt_task_queue::cancel_core(generic_task_result const & t) {
    switch (t->m_state.load()) {
        case task_result_state::WAITING:
            m_waiting.erase(t);
        case task_result_state::QUEUED:
            t->m_ex = std::make_exception_ptr(task_cancellation_exception(t));
            t->m_state = task_result_state::FAILED;
            propagate_failure(t);
            t->clear_task();
            return;
        case task_result_state::EXECUTING:
            for (auto & w : m_workers) {
                if (w->m_current_task == t) {
                    w->m_interrupt_flag->store(true);
                }
            }
            return;
        default: return;
    }
}
void mt_task_queue::cancel(generic_task_result const & t) {
    if (!t) return;
    unique_lock<mutex> lock(m_mutex);
    cancel_core(t);
}

bool mt_task_queue::empty_core() {
    for (auto & w : m_workers) {
        if (w->m_current_task)
            return false;
    }
    return m_queue.empty() && m_waiting.empty();
}

bool mt_task_queue::empty() {
    unique_lock<mutex> lock(m_mutex);
    return empty_core();
}

optional<generic_task_result> mt_task_queue::get_current_task() {
    unique_lock<mutex> lock(m_mutex);
    for (auto & w : m_workers) {
        if (w->m_current_task) {
            return optional<generic_task_result>(w->m_current_task);
        }
    }
    return optional<generic_task_result>();
}

generic_task_result mt_task_queue::dequeue() {
    lean_assert(!m_queue.empty());
    auto it = m_queue.begin();
    auto & highest_prio = it->second;
    lean_assert(!highest_prio.empty());
    auto result = std::move(highest_prio.front());
    highest_prio.pop_front();
    if (highest_prio.empty()) {
        m_queue.erase(it);
    }
    return result;
}

void mt_task_queue::enqueue(generic_task_result const & t) {
    lean_assert(t->m_state.load() < task_result_state::EXECUTING);
    lean_assert(t->m_task);
    t->m_state = task_result_state::QUEUED;
    m_queue[t->m_task->m_prio.m_prio].push_back(t);
    m_queue_added.notify_one();
}

void mt_task_queue::reprioritize(mt_tq_prioritizer const & p) {
    unique_lock<mutex> lock(m_mutex);
    m_prioritizer = p;
    reprioritize_core();
}

void mt_task_queue::reprioritize() {
    unique_lock<mutex> lock(m_mutex);
    reprioritize_core();
}

void mt_task_queue::reprioritize_core() {
    auto old_queues = m_queue;
    m_queue.clear();
    for (auto & q : old_queues) {
        for (auto & t : q.second) {
            if (t->m_task) {
                t->m_task->m_prio = m_prioritizer(t->m_task);
                enqueue(t);
            }
        }
    }
    for (auto & q : old_queues) for (auto & t : q.second) check_deps(t);

    for (auto & t : m_waiting) {
        if (t->m_task) {
            t->m_task->m_prio = m_prioritizer(t->m_task);
            check_deps(t);
        }
    }
}

void mt_task_queue::set_progress_callback(progress_cb const & cb) {
    unique_lock<mutex> lock(m_mutex);
    m_progress_cb = cb;
}

}
#endif
