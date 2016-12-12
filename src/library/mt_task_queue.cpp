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
#include "task_helper.h"

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
    for (auto & w : m_workers) w->m_thread->join();
}

void mt_task_queue::spawn_worker() {
    lean_assert(!m_shutting_down);
    auto this_worker = std::make_shared<worker_info>();
    this_worker->m_thread.reset(new lthread([=]() {
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
            if (unwrap(t)->m_state.load() != task_result_state::QUEUED) continue;

            unwrap(t)->m_state = task_result_state::EXECUTING;
            bool is_ok;
            auto cb = m_progress_cb;
            reset_interrupt();
            {
                flet<generic_task_result> _(this_worker->m_current_task, t);
                scoped_current_task scope_cur_task(&t);
                lock.unlock();
                if (cb) cb(unwrap(t)->m_task);
                is_ok = execute_task_with_scopes(unwrap(t));
                lock.lock();
            }
            reset_interrupt();

            unwrap(t)->m_state = is_ok ? task_result_state::FINISHED : task_result_state::FAILED;
            get_data(t).m_has_finished.notify_all();

            if (is_ok) {
                for (auto & rdep : get_data(t).m_reverse_deps) {
                    if (unwrap(rdep)->has_evaluated()) {
                        m_waiting.erase(rdep);
                    } else {
                        switch (unwrap(rdep)->m_state.load()) {
                            case task_result_state::WAITING:
                                if (check_deps(rdep)) {
                                    m_waiting.erase(rdep);
                                    if (!unwrap(rdep)->has_evaluated())
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

            unwrap(t)->clear_task();
            m_queue_removed.notify_all();
        }
    }));
    m_workers.push_back(this_worker);
}

void mt_task_queue::propagate_failure(generic_task_result const & tr) {
    lean_assert(unwrap(tr)->m_state.load() == task_result_state::FAILED);
    m_waiting.erase(tr);

    if (auto t = unwrap(tr)->m_task) {
        get_data(tr).m_has_finished.notify_all();

        for (auto & rdep : get_data(t).m_reverse_deps) {
            switch (unwrap(rdep)->m_state.load()) {
                case task_result_state::WAITING:
                case task_result_state::QUEUED:
                    unwrap(rdep)->m_ex = unwrap(tr)->m_ex;
                    unwrap(rdep)->m_state = task_result_state::FAILED;
                    propagate_failure(rdep);
                    break;
                default: break;
            }
        }
    }

    unwrap(tr)->clear_task();
}

void mt_task_queue::submit(generic_task_result const & t) {
    unique_lock<mutex> lock(m_mutex);
    check_interrupted();
    get_prio(t) = m_prioritizer(unwrap(t)->m_task);
    if (check_deps(t)) {
        if (!unwrap(t)->has_evaluated()) {
            enqueue(t);
        }
    } else {
        unwrap(t)->m_state = task_result_state::WAITING;
        m_waiting.insert(t);
    }
}

void mt_task_queue::bump_prio(generic_task_result const & t, task_priority const & new_prio) {
    if (unwrap(t)->m_task && new_prio < get_prio(t)) {
        switch (unwrap(t)->m_state.load()) {
        case task_result_state::QUEUED: {
            auto prio = get_prio(t).m_prio;
            auto &q = m_queue[prio];
            auto it = std::find(q.begin(), q.end(), t);
            lean_assert(it != q.end());
            q.erase(it);
            if (q.empty()) m_queue.erase(prio);

            get_prio(t).bump(new_prio);
            check_deps(t);
            enqueue(t);
            break;
        }
        case task_result_state::WAITING:
            get_prio(t).bump(new_prio);
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
        deps = unwrap(t)->m_task->get_dependencies();
    } catch (...) {}
    for (auto & dep : deps) {
        if (dep) bump_prio(dep, get_prio(t));
    }
    for (auto & dep : deps) {
        if (!dep) continue;
        switch (unwrap(dep)->m_state.load()) {
            case task_result_state::WAITING:
            case task_result_state::QUEUED:
            case task_result_state::EXECUTING:
                lean_assert(unwrap(dep)->m_task);
                get_data(dep).m_reverse_deps.push_back(t);
                return false;
            case task_result_state::FINISHED:
                break;
            case task_result_state::FAILED:
                unwrap(t)->m_ex = unwrap(dep)->m_ex;
                unwrap(t)->m_state = task_result_state::FAILED;
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
    if (g_current_task && unwrap(t)->m_task && get_prio(*g_current_task) < get_prio(t)) {
        bump_prio(t, get_prio(*g_current_task));
    }
    while (!unwrap(t)->has_evaluated()) {
        if (g_current_task) {
            scoped_add<int> inc_required(m_required_workers, +1);
            if (m_sleeping_workers == 0) {
                spawn_worker();
            } else {
                m_wake_up_worker.notify_one();
            }
            get_data(t).m_has_finished.wait(lock);
        } else {
            get_data(t).m_has_finished.wait(lock);
        }
    }
    switch (unwrap(t)->m_state.load()) {
        case task_result_state::FAILED: std::rethrow_exception(unwrap(t)->m_ex);
        case task_result_state::FINISHED: return;
        default: throw exception("invalid task state");
    }
}

void mt_task_queue::cancel_if(const std::function<bool(generic_task *)> & pred) { // NOLINT
    std::vector<generic_task_result> to_cancel;
    unique_lock<mutex> lock(m_mutex);

    for (auto & w : m_workers)
        if (w->m_current_task && pred(unwrap(w->m_current_task)->m_task))
            to_cancel.push_back(w->m_current_task);

    for (auto & q : m_queue)
        for (auto & t : q.second)
            if (unwrap(t)->m_task && pred(unwrap(t)->m_task))
                to_cancel.push_back(t);

    for (auto & t : m_waiting)
        if (unwrap(t)->m_task && pred(unwrap(t)->m_task))
            to_cancel.push_back(t);

    for (auto & t : to_cancel)
        cancel_core(t);
}

void mt_task_queue::cancel_core(generic_task_result const & t) {
    switch (unwrap(t)->m_state.load()) {
        case task_result_state::WAITING:
            m_waiting.erase(t);
        case task_result_state::QUEUED:
            unwrap(t)->m_ex = std::make_exception_ptr(task_cancellation_exception(t));
            unwrap(t)->m_state = task_result_state::FAILED;
            propagate_failure(t);
            unwrap(t)->clear_task();
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

void mt_task_queue::join() {
    unique_lock<mutex> lock(m_mutex);
    m_queue_removed.wait(lock, [=] { return empty_core(); });
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
    lean_assert(unwrap(t)->m_state.load() < task_result_state::EXECUTING);
    lean_assert(unwrap(t)->m_task);
    unwrap(t)->m_state = task_result_state::QUEUED;
    m_queue[get_prio(t).m_prio].push_back(t);
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
            if (unwrap(t)) {
                get_prio(t) = m_prioritizer(unwrap(t)->m_task);
                enqueue(t);
            }
        }
    }
    for (auto & q : old_queues) for (auto & t : q.second) check_deps(t);

    for (auto & t : m_waiting) {
        if (unwrap(t)->m_task) {
            get_prio(t) = m_prioritizer(unwrap(t)->m_task);
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
