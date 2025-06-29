/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <chrono>
#include <functional>
#include <lean/lean.h>

#ifndef LEAN_STACK_BUFFER_SPACE
#define LEAN_STACK_BUFFER_SPACE 128*1024  // 128 Kb
#endif

namespace lean {
namespace chrono = std::chrono;
};

#if defined(LEAN_MULTI_THREAD)
#include <thread>
#include <mutex>
#include <shared_mutex>
#include <atomic>
#include <condition_variable>
#define LEAN_THREAD_LOCAL thread_local

namespace lean {
using std::thread;
using std::mutex;
using std::recursive_mutex;
using std::shared_timed_mutex;
using std::atomic;
using std::atomic_bool;
using std::atomic_ushort;
using std::atomic_uint;
using std::atomic_uchar;
using std::condition_variable;
using std::lock_guard;
using std::unique_lock;
using std::atomic_load;
using std::atomic_load_explicit;
using std::atomic_fetch_add_explicit;
using std::atomic_fetch_sub_explicit;
using std::memory_order_relaxed;
using std::memory_order_release;
using std::memory_order_acquire;
using std::memory_order_acq_rel;
using std::memory_order_seq_cst;
using std::atomic_thread_fence;
namespace this_thread = std::this_thread;
inline unsigned hardware_concurrency() { return std::thread::hardware_concurrency(); }
/** Simple thread class that allows us to set the thread stack size.
    We implement it using pthreads on OSX/Linux and WinThreads on Windows. */
class LEAN_EXPORT lthread {
    static size_t m_thread_stack_size;
    struct imp;
    std::unique_ptr<imp> m_imp;
public:
    lthread(std::function<void(void)> const & p);
    ~lthread();
    void join();
    static void set_thread_stack_size(size_t sz);
    static size_t get_thread_stack_size();
};
}

#else
// NO MULTI THREADING SUPPORT
#include <utility>
#include <cstdlib>
#define LEAN_THREAD_LOCAL
namespace lean {
constexpr int memory_order_relaxed = 0;
constexpr int memory_order_release = 0;
constexpr int memory_order_acquire = 0;
constexpr int memory_order_acq_rel = 0;
constexpr int memory_order_seq_cst = 0;
inline void atomic_thread_fence(int ) {}
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
    friend T atomic_load_explicit(atomic const * a, int) { return a->m_value; }
    friend T atomic_fetch_add_explicit(atomic * a, T const & v, int ) { T r(a->m_value); a->m_value += v; return r; }
    friend T atomic_fetch_sub_explicit(atomic * a, T const & v, int ) { T r(a->m_value); a->m_value -= v; return r; }
    T exchange(T desired) { T old = m_value; m_value = desired; return old; }
    bool compare_exchange_strong(T & expected, T desired) {
        if (m_value == expected) {
            m_value = desired;
            return true;
        } else {
            expected = m_value;
            return false;
        }
    }
};
typedef atomic<unsigned short> atomic_ushort;
typedef atomic<unsigned char>  atomic_uchar;
typedef atomic<bool>           atomic_bool;
typedef atomic<unsigned>       atomic_uint;
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
class lthread {
public:
    lthread(std::function<void(void)> const & p) { p(); }
    ~lthread() {}
    void join() {}
    static void set_thread_stack_size(size_t) {}
    static size_t get_thread_stack_size() { return 0; }
};
class this_thread {
public:
    static void sleep_for(chrono::milliseconds const &) {}
    static thread::id get_id() { return 0; }
    static void yield() {}
};
class mutex {
public:
    void lock() {}
    bool try_lock() { return true; }
    void unlock() {}
};
class recursive_mutex {
public:
    void lock() {}
    bool try_lock() { return true; }
    void unlock() {}
};
class shared_timed_mutex {
public:
    void lock() {}
    bool try_lock() { return true; }
    void unlock() {}
    void lock_shared() {}
    bool try_lock_shared() { return true; }
    void unlock_shared() {}
};
class condition_variable {
public:
    template<typename Lock> void wait(Lock const &) {}
    template<typename Lock, typename F> void wait(Lock const &, F) {}
    template<typename Lock> void wait_for(Lock const &, chrono::milliseconds const &) {}
    void notify_all() {}
    void notify_one() {}
};
template<typename T> class lock_guard {
public:
    lock_guard(T const &) {}
    ~lock_guard() {}
};
template<typename T> class unique_lock {
public:
    unique_lock(T const &) {}
    ~unique_lock() {}
    void lock() {}
    void unlock() {}
};
inline unsigned hardware_concurrency() { return 1; }
}
#endif

#ifdef _MSC_VER
#define LEAN_THREAD_PTR(T, V) static __declspec(thread) T * V = nullptr
#define LEAN_THREAD_EXTERN_PTR(T, V) extern __declspec(thread) T * V
#define LEAN_THREAD_GLOBAL_PTR(T, V) __declspec(thread) T * V = nullptr
#define LEAN_THREAD_VALUE(T, V, VAL) static __declspec(thread) T V = VAL
#else
#define LEAN_THREAD_PTR(T, V) static __thread T * V = nullptr
#define LEAN_THREAD_EXTERN_PTR(T, V) extern __thread T * V
#define LEAN_THREAD_GLOBAL_PTR(T, V) __thread T * V = nullptr
#define LEAN_THREAD_VALUE(T, V, VAL) static __thread T V = VAL
#endif

#define MK_THREAD_LOCAL_GET(T, GETTER_NAME, DEF_VALUE)                  \
LEAN_THREAD_PTR(T, GETTER_NAME ## _tlocal);                             \
static void finalize_ ## GETTER_NAME(void * p) {                        \
    delete reinterpret_cast<T*>(p);                                     \
    GETTER_NAME ## _tlocal = nullptr;                                   \
}                                                                       \
static T & GETTER_NAME() {                                              \
    if (!GETTER_NAME ## _tlocal) {                                      \
        GETTER_NAME ## _tlocal  = new T(DEF_VALUE);                     \
        register_thread_finalizer(finalize_ ## GETTER_NAME, GETTER_NAME ## _tlocal); \
    }                                                                   \
    return *(GETTER_NAME ## _tlocal);                                   \
}

#define MK_THREAD_LOCAL_GET_DEF(T, GETTER_NAME)                         \
LEAN_THREAD_PTR(T, GETTER_NAME ## _tlocal);                             \
static void finalize_ ## GETTER_NAME(void * p) {                        \
    delete reinterpret_cast<T*>(p);                                     \
    GETTER_NAME ## _tlocal = nullptr;                                   \
}                                                                       \
static T & GETTER_NAME() {                                              \
    if (!GETTER_NAME ## _tlocal) {                                      \
        GETTER_NAME ## _tlocal  = new T();                              \
        register_thread_finalizer(finalize_ ## GETTER_NAME, GETTER_NAME ## _tlocal); \
    }                                                                   \
    return *(GETTER_NAME ## _tlocal);                                   \
}

namespace lean {
// module initializer pair (NOT for initializing individual threads!)
void initialize_thread();
void finalize_thread();

// thread initializer pair, for reverse FFI
extern "C" LEAN_EXPORT void lean_initialize_thread();
extern "C" LEAN_EXPORT void lean_finalize_thread();

typedef void (*thread_finalizer)(void *); // NOLINT
LEAN_EXPORT void register_post_thread_finalizer(thread_finalizer fn, void * p);
LEAN_EXPORT void register_thread_finalizer(thread_finalizer fn, void * p);
LEAN_EXPORT void run_thread_finalizers();
LEAN_EXPORT void run_post_thread_finalizers();
LEAN_EXPORT void delete_thread_finalizer_manager();

LEAN_EXPORT bool in_thread_finalization();

/**
    \brief Add \c fn to the list of functions used to reset thread local storage.

    This function must only be invoked during initialization.

    We use these functions to reset thread local storage that
    contains cached data that may not be valid anymore.

    \see reset_thread_local */
LEAN_EXPORT void register_thread_local_reset_fn(std::function<void()> fn);

/**
   \brief Reset thread local storage that contains cached
   data that may not be valid anymore.

   We invoke this function before processing a command
   and before executing a task. */
LEAN_EXPORT void reset_thread_local();
}
