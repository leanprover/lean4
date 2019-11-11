/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/timer.h"

#if defined(LEAN_MULTI_THREAD)
namespace lean {
constexpr chrono::steady_clock::duration accuracy = chrono::milliseconds(10);

single_timer::single_timer():
    m_shutting_down(false),
    m_thread(std::bind(&single_timer::worker, this)) {}

single_timer::~single_timer() {
    {
        unique_lock<mutex> lock(m_mutex);
        m_shutting_down = true;
        m_timer_changed.notify_one();
    }
    m_thread.join();
}

void single_timer::worker() {
    unique_lock<mutex> lock(m_mutex);
    while (!m_shutting_down) {
        auto now = chrono::steady_clock::now();
        if (m_time && *m_time <= now + accuracy) {
            m_time = optional<chrono::steady_clock::time_point>();
            if (auto cb = std::move(m_cb)) {
                lock.unlock();
                cb();
                lock.lock();
            }
        } else if (m_time) {
            m_timer_changed.wait_for(lock, *m_time - now);
        } else {
            m_timer_changed.wait(lock);
        }
    }
}

void single_timer::set(chrono::steady_clock::time_point const & time, callback const & cb, bool overwrite) {
    unique_lock<mutex> lock(m_mutex);
    if (overwrite || !m_time) {
        m_time = optional<chrono::steady_clock::time_point>(time);
        m_cb = cb;
        m_timer_changed.notify_one();
    }
}

void single_timer::reset() {
    unique_lock<mutex> lock(m_mutex);
    m_time = optional<chrono::steady_clock::time_point>();
    m_cb = nullptr;
    m_timer_changed.notify_one();
}
}
#endif
