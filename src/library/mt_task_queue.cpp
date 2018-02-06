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

LEAN_THREAD_PTR(gtask, g_current_task);
struct scoped_current_task : flet<gtask *> {
    scoped_current_task(gtask * t) : flet(g_current_task, t) {}
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

mt_task_queue::mt_task_queue(unsigned num_workers) : m_required_workers(num_workers) {}

mt_task_queue::~mt_task_queue() {
    unique_lock<mutex> lock(m_mutex);
    m_queue_changed.wait(lock, [=] { return empty_core(); });
    m_shutting_down = true;
    m_queue_added.notify_all();
    m_queue_changed.notify_all();
    m_wake_up_worker.notify_all();
    m_shut_down_cv.wait(lock, [=] { return m_workers.empty(); });
}


template <class Fn>
void mt_task_queue::mt_sched_info::wait(unique_lock<mutex> & lock, Fn && fn) {
    if (!m_has_finished)
        m_has_finished = std::make_shared<condition_variable>();
    auto has_finished = m_has_finished;
    has_finished->wait(lock, fn);
}

void mt_task_queue::mt_sched_info::notify() {
    if (m_has_finished) m_has_finished->notify_all();
}

bool mt_task_queue::empty_core() {
    for (auto & w : m_workers) {
        if (w->m_current_task)
            return false;
    }
    return m_queue.empty() && m_waiting.empty();
}

void mt_task_queue::notify_queue_changed() {
    m_queue_changed.notify_all();
}

constexpr chrono::milliseconds g_worker_max_idle_time = chrono::milliseconds(1000);

void mt_task_queue::spawn_worker() {
    lean_always_assert(!m_shutting_down);
    auto this_worker = std::make_shared<worker_info>();
    m_workers.push_back(this_worker);
    m_required_workers--;
    this_worker->m_thread.reset(new lthread([this, this_worker]() {
        save_stack_info(false);

        unique_lock<mutex> lock(m_mutex);
        while (true) {
            if (m_shutting_down) {
                break;
            }
            if (m_required_workers < 0) {
                scoped_add<int> inc_required(m_required_workers, +1);
                scoped_add<unsigned> inc_sleeping(m_sleeping_workers, +1);
                if (m_wake_up_worker.wait_for(lock, g_worker_max_idle_time,
                                              [&] { return m_required_workers >= 1 || m_shutting_down; })) {
                    continue;
                } else {
                    break;
                }
            }
            if (m_queue.empty()) {
                if (m_queue_added.wait_for(lock, g_worker_max_idle_time,
                                           [&] { return !m_queue.empty() || m_shutting_down; })) {
                    continue;
                } else {
                    break;
                }
            }

            auto t = dequeue();
            if (get_state(t).load() != task_state::Queued) continue;

            get_state(t) = task_state::Running;
            reset_heartbeat();
            reset_thread_local();
            {
                flet<gtask> _(this_worker->m_current_task, t);
                scoped_current_task scope_cur_task(&t);
                notify_queue_changed();
                lock.unlock();
                execute(t);
                lock.lock();
            }
            reset_heartbeat();

            handle_finished(t);

            notify_queue_changed();
        }

        // We need to run the finalizers while the lock is held,
        // otherwise we risk a race condition at the end of the program.
        // We would finalize in the thread, while we call the finalize() function.
        run_thread_finalizers();
        run_post_thread_finalizers();

        m_workers.erase(std::find(m_workers.begin(), m_workers.end(), this_worker));
        m_required_workers++;
        m_shut_down_cv.notify_all();
    }));
}

void mt_task_queue::handle_finished(gtask const & t) {
    lean_always_assert(get_state(t).load() > task_state::Running);
    lean_always_assert(get_data(t));

    if (!get_data(t)->m_sched_info)
        return;  // task has never been submitted

    m_waiting.erase(t);
    get_sched_info(t).notify();

    for (auto & rdep : get_sched_info(t).m_reverse_deps) {
        switch (get_state(rdep).load()) {
            case task_state::Waiting: case task_state::Queued:
                if (check_deps(rdep)) {
                    m_waiting.erase(rdep);
                    if (get_state(rdep).load() < task_state::Running) {
                        lean_always_assert(get_data(rdep));
                        // TODO(gabriel): we need to give up the lock on m_mutex for this
                        if (false && get_data(rdep)->m_flags.m_eager_execution) {
                            get_state(rdep) = task_state::Running;
                            execute(rdep);
                            handle_finished(rdep);
                        } else {
                            enqueue(rdep);
                        }
                    }
                }
                break;
            case task_state::Failed:
                // TODO(gabriel): removed failed tasks from reverse dependency lists?
                m_waiting.erase(rdep);
                break;
            case task_state::Success:
                // this can happen if a task occurs in more than one reverse dependency list,
                // or gets submitted more than once
                break;
            default: lean_unreachable();
        }
    }

    clear(t);
}

void mt_task_queue::submit(gtask const & t, unsigned prio) {
    if (!t || get_state(t).load() >= task_state::Running) return;
    unique_lock<mutex> lock(m_mutex);
    submit_core(t, prio);
}
void mt_task_queue::submit_core(gtask const & t, unsigned prio) {
    if (!t) return;
    switch (get_state(t).load()){
        case task_state::Created:
            get_data(t)->m_sched_info.reset(new mt_sched_info(prio));
            if (check_deps(t)) {
                if (get_state(t).load() < task_state::Running) {
                    // TODO(gabriel): we need to give up the lock on m_mutex for this
                    if (false && get_data(t)->m_flags.m_eager_execution) {
                        get_state(t) = task_state::Running;
                        execute(t);
                        handle_finished(t);
                    } else {
                        enqueue(t);
                    }
                }
            } else {
                get_state(t) = task_state::Waiting;
                m_waiting.insert(t);
                notify_queue_changed();
            }
            break;
        case task_state::Waiting: case task_state::Queued:
            bump_prio(t, prio);
            break;
        case task_state::Running: case task_state::Failed: case task_state::Success:
            break;
    }
    lean_always_assert(get_state(t).load() >= task_state::Waiting);
}

void mt_task_queue::bump_prio(gtask const & t, unsigned new_prio) {
    switch (get_state(t).load()) {
        case task_state::Queued:
            if (new_prio < get_prio(t)) {
                auto prio = get_prio(t);
                auto &q = m_queue[prio];
                auto it = std::find(q.begin(), q.end(), t);
                lean_always_assert(it != q.end());
                q.erase(it);
                if (q.empty()) m_queue.erase(prio);

                get_prio(t) = std::min(get_prio(t), new_prio);
                check_deps(t);
                enqueue(t);
            }
            break;
        case task_state::Waiting:
            if (new_prio < get_prio(t)) {
                get_prio(t) = std::min(get_prio(t), new_prio);
                check_deps(t);
            }
            break;
        case task_state::Running: case task_state::Failed: case task_state::Success:
            break;
        default: lean_unreachable();
    }
}

bool mt_task_queue::check_deps(gtask const & t) {
    check_stack("mt_task_queue::check_deps");
    lean_always_assert(get_data(t));

    buffer<gtask> deps;
    try {
        get_data(t)->m_imp->get_dependencies(deps);
    } catch (...) {}

    auto prio = get_prio(t);
    for (auto & dep : deps) {
        if (dep) {
            submit_core(dep, prio);
            bump_prio(dep, prio);
        }
    }

    for (auto & dep : deps) {
        if (!dep) continue;
        switch (get_state(dep).load()) {
            case task_state::Waiting: case task_state::Queued: case task_state::Running:
                lean_always_assert(get_imp(dep));
                get_sched_info(dep).m_reverse_deps.push_back(t);
                return false;
            case task_state::Success:
                break;
            case task_state::Failed:
                break;
            default: lean_unreachable();
        }
    }
    return true;
}

void mt_task_queue::wait_for_finish(gtask const & t) {
    if (!t || get_state(t).load() > task_state::Running) return;
    unique_lock<mutex> lock(m_mutex);
    submit_core(t, get_default_prio());
    if (get_state(t).load() <= task_state::Running) {
        int additionally_required_workers = 0;
        if (g_current_task) {
            additionally_required_workers++;
            if (m_sleeping_workers == 0) {
                spawn_worker();
            } else {
                m_wake_up_worker.notify_one();
            }
        }
        scoped_add<int> inc_required(m_required_workers, additionally_required_workers);
        get_sched_info(t).wait(lock, [&] {
            return get_state(t).load() > task_state::Running;
        });
    }
    switch (get_state(t).load()) {
        case task_state::Failed: case task_state::Success: return;
        default: throw exception("invalid task state");
    }
}

void mt_task_queue::cancel_core(gtask const & t) {
    if (!t) return;
    switch (get_state(t).load()) {
        case task_state::Waiting:
            m_waiting.erase(t);
            /* fall-thru */
        case task_state::Created: case task_state::Queued:
            fail(t, std::make_exception_ptr(cancellation_exception()));
            handle_finished(t);
            return;
        default: return;
    }
}
void mt_task_queue::fail_and_dispose(gtask const & t) {
    if (!t) return;
    unique_lock<mutex> lock(m_mutex);
    cancel_core(t);
}

void mt_task_queue::join() {
    unique_lock<mutex> lock(m_mutex);
    m_queue_changed.wait(lock, [=] { return empty_core(); });
}

gtask mt_task_queue::dequeue() {
    lean_always_assert(!m_queue.empty());
    auto it = m_queue.begin();
    auto & highest_prio = it->second;
    lean_always_assert(!highest_prio.empty());
    auto result = std::move(highest_prio.front());
    highest_prio.pop_front();
    if (highest_prio.empty()) {
        m_queue.erase(it);
    }
    return result;
}

void mt_task_queue::enqueue(gtask const & t) {
    lean_always_assert(get_state(t).load() < task_state::Running);
    lean_always_assert(get_imp(t));
    get_state(t) = task_state::Queued;
    m_queue[get_prio(t)].push_back(t);
    if (m_required_workers > 0) {
        spawn_worker();
    } else {
        m_queue_added.notify_one();
    }
    notify_queue_changed();
}

void mt_task_queue::evacuate() {
    unique_lock<mutex> lock(m_mutex);
    for (auto & q : m_queue) for (auto & t : q.second) cancel_core(t);

    buffer<gtask> to_cancel; // copy because of iterator invalidation
    for (auto & t : m_waiting) to_cancel.push_back(t);
    for (auto & t : to_cancel) cancel_core(t);
}

void mt_task_queue::submit(gtask const & t) {
    submit(t, get_default_prio());
}

unsigned mt_task_queue::get_default_prio() {
    if (g_current_task && get_imp(*g_current_task)) {
        return get_prio(*g_current_task);
    } else {
        return 0;
    }
}

}
#endif
