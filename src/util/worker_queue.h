/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <functional>
#include <vector>
#include "util/buffer.h"
#include "util/thread.h"
#include "util/interrupt.h"
#include "util/optional.h"
#include "util/exception.h"

namespace lean {
template<typename T>
class worker_queue {
    typedef std::function<T()>                    task;
    typedef std::unique_ptr<interruptible_thread> thread_ptr;
    typedef std::unique_ptr<throwable>            exception_ptr;
    std::vector<thread_ptr>    m_threads;
    std::vector<exception_ptr> m_thread_exceptions;
    std::vector<task>          m_todo;
    std::vector<T>             m_result;
    mutex                      m_result_mutex;
    mutex                      m_todo_mutex;
    condition_variable         m_todo_cv;
    unsigned                   m_todo_qhead;
    atomic<bool>               m_done;
    atomic<int>                m_failed_thread; // if >= 0, it has the index of a failing thread.
    atomic<bool>               m_interrupted;

    optional<task> next_task() {
        while (true) {
            check_interrupted();
            unique_lock<mutex> lk(m_todo_mutex);
            if (m_todo_qhead < m_todo.size()) {
                task r = m_todo[m_todo_qhead];
                m_todo_qhead++;
                return optional<task>(r);
            } else if (m_done) {
                return optional<task>();
            } else {
                m_todo_cv.wait(lk);
            }
        }
    }

    void add_result(T const & v) {
        lock_guard<mutex> l(m_result_mutex);
        m_result.push_back(v);
    }

public:
    template<typename F>
    worker_queue(unsigned num_threads, F const & f):m_todo_qhead(0), m_done(false), m_failed_thread(-1), m_interrupted(false) {
#ifndef LEAN_MULTI_THREAD
        num_threads = 0;
#endif
        for (unsigned i = 0; i < num_threads; i++)
            m_thread_exceptions.push_back(exception_ptr(nullptr));
        for (unsigned i = 0; i < num_threads; i++) {
            m_threads.push_back(std::unique_ptr<interruptible_thread>(new interruptible_thread([=]() {
                            f();
                            try {
                                while (auto t = next_task()) {
                                    add_result((*t)());
                                }
                                m_todo_cv.notify_all();
                            } catch (interrupted &) {
                            } catch (throwable & ex) {
                                m_thread_exceptions[i].reset(ex.clone());
                                m_failed_thread = i;
                            } catch (...) {
                                m_thread_exceptions[i].reset(new exception("thread failed for unknown reasons"));
                                m_failed_thread = i;
                            }
                        })));
        }
    }
    worker_queue(unsigned num_threads):worker_queue(num_threads, [](){ return; }) {}
    ~worker_queue() { if (!m_done) join(); }

    void add(std::function<T()> const & fn) {
        lean_assert(!m_done);
        {
            lock_guard<mutex> l(m_todo_mutex);
            m_todo.push_back(fn);
        }
        m_todo_cv.notify_one();
    }

    std::vector<T> const & join() {
        lean_assert(!m_done);
        m_done = true;
        if (m_threads.empty()) {
            for (auto const & fn : m_todo) {
                m_result.push_back(fn());
            }
            m_todo.clear();
        } else {
            try {
                while (auto t = next_task()) {
                    add_result((*t)());
                }
                m_todo_cv.notify_all();
                for (thread_ptr & t : m_threads)
                    t->join();
            } catch (...) {
                for (auto & th : m_threads)
                    th->request_interrupt();
                for (auto & th : m_threads)
                    th->join();
                throw;
            }
            if (m_failed_thread >= 0)
                m_thread_exceptions[m_failed_thread]->rethrow();
            if (m_interrupted)
                throw interrupted();
        }
        return m_result;
    }

    void interrupt() {
        m_interrupted = true;
        for (auto & t : m_threads)
            t->request_interrupt();
    }

    bool done() const { return m_done; }
};
}
