/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#if defined(LEAN_MULTI_THREAD)
#include <thread>
#include <mutex>
#include <atomic>
#include <condition_variable>
#define LEAN_THREAD_LOCAL thread_local
namespace lean {
using std::thread;
using std::mutex;
using std::atomic;
using std::atomic_bool;
using std::atomic_ushort;
using std::condition_variable;
using std::lock_guard;
using std::unique_lock;
using std::atomic_load;
using std::atomic_fetch_add_explicit;
using std::atomic_fetch_sub_explicit;
using std::memory_order_relaxed;
namespace this_thread = std::this_thread;
}
#else
#include <utility>
#include <chrono>
#define LEAN_THREAD_LOCAL
namespace lean {
constexpr int memory_order_relaxed = 0;
template<typename T>
class atomic {
    T m_value;
public:
    atomic(T const & v = T()):m_value(v) {}
    atomic(T && v):m_value(std::forward<T>(v)) {}
    atomic(atomic const & v):m_value(v.m_value) {}
    atomic(atomic && v):m_value(std::forward<T>(v.m_value)) {}
    atomic & operator=(T const & v) { m_value = v; return *this; }
    atomic & operator=(T && v) { m_value = std::forward<T>(v); return *this; }
    atomic & operator=(atomic const & v) { m_value = v.m_value; return *this; }
    atomic & operator=(atomic && v) { m_value = std::forward<T>(v.m_value); return *this; }
    operator T() const { return m_value; }
    void store(T const & v) { m_value = v; }
    T load() const { return m_value; }
    atomic & operator|=(T const & v) { m_value |= v; return *this; }
    atomic & operator+=(T const & v) { m_value += v; return *this; }
    atomic & operator-=(T const & v) { m_value -= v; return *this; }
    atomic & operator++() { ++m_value; return *this; }
    atomic   operator++(int ) { atomic tmp(*this); ++m_value; return tmp; }
    atomic & operator--() { --m_value; return *this; }
    atomic   operator--(int ) { atomic tmp(*this); --m_value; return tmp; }
    friend T atomic_load(atomic const * a) { return a->m_value; }
    friend T atomic_fetch_add_explicit(atomic * a, T const & v, int ) { T r(a->m_value); a->m_value += v; return r; }
    friend T atomic_fetch_sub_explicit(atomic * a, T const & v, int ) { T r(a->m_value); a->m_value -= v; return r; }
};
typedef atomic<unsigned short> atomic_ushort;
typedef atomic<bool>           atomic_bool;
class thread {
public:
    thread() {}
    template<typename Function, typename... Args>
    thread(Function && fun, Args &&... args) {
        fun(std::forward<Args>(args)...);
    }
    typedef unsigned id;
    bool joinable() const { return true; }
    void join() {}
};
class this_thread {
public:
    template<typename Rep, typename Period>
    static void sleep_for(std::chrono::duration<Rep, Period> const &) {}
    static thread::id get_id() { return 0; }
    static void yield() {}
};
class mutex {
public:
    void lock() {}
    void unlock() {}
};
class condition_variable {
public:
    template<typename Lock> void wait(Lock const &) {}
    void notify_all() {}
    void notify_one() {}
};
template<typename T> class lock_guard {
public:
    lock_guard(T const &) {}
};
template<typename T> class unique_lock {
public:
    unique_lock(T const &) {}
};
}
#endif
