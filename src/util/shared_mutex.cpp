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
#include "util/debug.h"
#include "util/shared_mutex.h"

namespace lean {
#if defined(LEAN_MULTI_THREAD)
shared_mutex::shared_mutex():m_rw_counter(0), m_state(0) {}
shared_mutex::~shared_mutex() {
    lock_guard<mutex> lock(m_mutex);
}

void shared_mutex::lock() {
    unique_lock<mutex> lock(m_mutex);
    if (m_rw_owner == this_thread::get_id()) {
        m_rw_counter++;
        return; // already has the lock
    }
    while (m_state & write_entered)
        m_gate1.wait(lock);
    m_state |= write_entered;
    while (m_state & readers)
        m_gate2.wait(lock);
    lean_assert(m_rw_counter == 0);
    m_rw_owner   = this_thread::get_id();
    m_rw_counter = 1;
}

bool shared_mutex::try_lock() {
    unique_lock<mutex> lock(m_mutex);
    if (m_rw_owner == this_thread::get_id()) {
        m_rw_counter++;
        return true; // already has the lock
    }
    if (m_state == 0) {
        m_state      = write_entered;
        lean_assert(m_rw_counter == 0);
        m_rw_owner   = this_thread::get_id();
        m_rw_counter = 1;
        return true;
    }
    return false;
}

void shared_mutex::unlock() {
    lock_guard<mutex> lock(m_mutex);
    lean_assert(m_rw_owner == this_thread::get_id());
    lean_assert(m_rw_counter > 0);
    m_rw_counter--;
    if (m_rw_counter > 0)
        return; // keep the lock
    m_rw_owner = thread::id(); // reset owner
    lean_assert(m_rw_counter == 0);
    lean_assert(m_rw_owner != this_thread::get_id());
    m_state = 0;
    m_gate1.notify_all();
}

void shared_mutex::lock_shared() {
    unique_lock<mutex> lock(m_mutex);
    if (m_rw_owner == this_thread::get_id()) {
        lean_assert(m_rw_counter > 0);
        m_rw_counter++;
        return; // already has the lock
    }
    while ((m_state & write_entered) || (m_state & readers) == readers)
        m_gate1.wait(lock);
    unsigned num_readers = (m_state & readers) + 1;
    m_state &= ~readers;
    m_state |= num_readers;
}

bool shared_mutex::try_lock_shared() {
    unique_lock<mutex> lock(m_mutex);
    if (m_rw_owner == this_thread::get_id()) {
        lean_assert(m_rw_counter > 0);
        m_rw_counter++;
        return true; // already has the lock
    }
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
    lock_guard<mutex> lock(m_mutex);
    if (m_rw_owner == this_thread::get_id()) {
        // if we have a rw (aka unshared) lock, then
        // the shared lock must be nested.
        lean_assert(m_rw_counter > 1);
        m_rw_counter--;
        return;
    }
    lean_assert(m_rw_counter == 0);
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
#endif
}
