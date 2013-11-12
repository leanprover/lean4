/**
   Copyright (c) 2013 Microsoft Corporation. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.

   Author: Leonardo de Moura

   C++11 does not support std::shared_mutex and std::shared_lock yet.
   This piece of code is based on the proposal submitted to the C++
   standardization committee. The proposal was written by Howard
   Hinnant. The proposal is also part of the Boost library which is
   licensed under http://www.boost.org/LICENSE_1_0.txt
*/
#include "util/shared_mutex.h"

namespace lean {
shared_mutex::shared_mutex():m_state(0) {}
shared_mutex::~shared_mutex() {
    std::lock_guard<std::mutex> lock(m_mutex);
}

void shared_mutex::lock() {
    std::unique_lock<std::mutex> lock(m_mutex);
    while (m_state & write_entered)
        m_gate1.wait(lock);
    m_state |= write_entered;
    while (m_state & readers)
        m_gate2.wait(lock);
}

bool shared_mutex::try_lock() {
    std::unique_lock<std::mutex> lock(m_mutex);
    if (m_state == 0) {
        m_state = write_entered;
        return true;
    }
    return false;
}

void shared_mutex::unlock() {
    std::lock_guard<std::mutex> lock(m_mutex);
    m_state = 0;
    m_gate1.notify_all();
}

void shared_mutex::lock_shared() {
    std::unique_lock<std::mutex> lock(m_mutex);
    while ((m_state & write_entered) || (m_state & readers) == readers)
        m_gate1.wait(lock);
    unsigned num_readers = (m_state & readers) + 1;
    m_state &= ~readers;
    m_state |= num_readers;
}

bool shared_mutex::try_lock_shared() {
    std::unique_lock<std::mutex> lock(m_mutex);
    unsigned num_readers = m_state & readers;
    if (!(m_state & write_entered) && num_readers != readers) {
        ++num_readers;
        m_state &= ~readers;
        m_state |= num_readers;
        return true;
    }
    return false;
}

void shared_mutex::unlock_shared() {
    std::lock_guard<std::mutex> lock(m_mutex);
    unsigned num_readers = (m_state & readers) - 1;
    m_state &= ~readers;
    m_state |= num_readers;
    if (m_state & write_entered) {
        if (num_readers == 0)
            m_gate2.notify_one();
    } else {
        if (num_readers == readers - 1)
            m_gate1.notify_one();
    }
}
}
