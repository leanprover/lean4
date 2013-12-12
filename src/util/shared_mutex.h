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
#pragma once
#include <climits>
#include "util/thread.h"

namespace lean {
#if defined(LEAN_MULTI_THREAD)
class shared_mutex {
    mutex                   m_mutex;
    thread::id              m_rw_owner;
    unsigned                m_rw_counter;
    condition_variable      m_gate1;
    condition_variable      m_gate2;
    unsigned                m_state;

    static constexpr unsigned write_entered = 1u << (sizeof(unsigned)*8 - 1);
    static constexpr unsigned readers       = ~write_entered;

public:
    shared_mutex();
    ~shared_mutex();

    shared_mutex(shared_mutex const &) = delete;
    shared_mutex(shared_mutex &&) = delete;
    shared_mutex& operator=(shared_mutex const &) = delete;
    shared_mutex&& operator=(shared_mutex &&) = delete;

    void lock();
    bool try_lock();
    void unlock();

    void lock_shared();
    bool try_lock_shared();
    void unlock_shared();
};
#else
class shared_mutex {
public:
    shared_mutex() {}
    shared_mutex(shared_mutex const &) = delete;
    shared_mutex(shared_mutex &&) = delete;
    shared_mutex& operator=(shared_mutex const &) = delete;
    shared_mutex&& operator=(shared_mutex &&) = delete;
    void lock() {}
    bool try_lock() { return true; }
    void unlock() {}

    void lock_shared() {}
    bool try_lock_shared() { return true; }
    void unlock_shared() {}
};
#endif

class shared_lock {
    shared_mutex & m_mutex;
public:
    shared_lock(shared_mutex & m):m_mutex(m) { m_mutex.lock_shared(); }
    ~shared_lock() { m_mutex.unlock_shared(); }
};

class exclusive_lock {
    shared_mutex & m_mutex;
public:
    exclusive_lock(shared_mutex & m):m_mutex(m) { m_mutex.lock(); }
    ~exclusive_lock() { m_mutex.unlock(); }
};
}
