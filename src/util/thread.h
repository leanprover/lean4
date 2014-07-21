/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#if defined(LEAN_MULTI_THREAD)
#if !defined(LEAN_USE_BOOST)
// MULTI THREADING SUPPORT BASED ON THE STANDARD LIBRARY
#include <thread>
#include <mutex>
#include <atomic>
#include <condition_variable>
#include <chrono>
#define LEAN_THREAD_LOCAL thread_local
namespace lean {
inline void set_thread_stack_size(size_t ) {}
using std::thread;
using std::mutex;
using std::recursive_mutex;
using std::atomic;
using std::atomic_bool;
using std::atomic_ushort;
using std::atomic_uint;
using std::atomic_uchar;
using std::condition_variable;
using std::lock_guard;
using std::unique_lock;
using std::atomic_load;
using std::atomic_fetch_add_explicit;
using std::atomic_fetch_sub_explicit;
using std::memory_order_relaxed;
using std::memory_order_release;
using std::memory_order_acquire;
using std::atomic_thread_fence;
namespace chrono      = std::chrono;
namespace this_thread = std::this_thread;
}
#else
// MULTI THREADING SUPPORT BASED ON THE BOOST LIBRARY
#include <boost/thread.hpp>
#define LEAN_THREAD_LOCAL thread_local
namespace lean {
void set_thread_stack_size(size_t );
boost::thread::attributes const & get_thread_attributes();
using boost::thread;
using boost::mutex;
using boost::recursive_mutex;
using boost::atomic;
using boost::memory_order_relaxed;
using boost::memory_order_acquire;
using boost::memory_order_release;
using boost::condition_variable;
using boost::unique_lock;
using boost::lock_guard;
using boost::atomic_thread_fence;
namespace chrono      = boost::chrono;
namespace this_thread = boost::this_thread;
typedef atomic<bool>           atomic_bool;
typedef atomic<unsigned short> atomic_ushort;
typedef atomic<unsigned char>  atomic_uchar;
typedef atomic<unsigned>       atomic_uint;
template<typename T> T atomic_load(atomic<T> const * a) { return a->load(); }
template<typename T> T atomic_fetch_add_explicit(atomic<T> * a, T v, boost::memory_order mo) { return a->fetch_add(v, mo); }
template<typename T> T atomic_fetch_sub_explicit(atomic<T> * a, T v, boost::memory_order mo) { return a->fetch_sub(v, mo); }
}
#endif
#else
// NO MULTI THREADING SUPPORT
#include <utility>
#include <cstdlib>
#define LEAN_THREAD_LOCAL
namespace lean {
inline void set_thread_stack_size(size_t ) {}
namespace chrono {
typedef unsigned milliseconds;
}
constexpr int memory_order_relaxed = 0;
constexpr int memory_order_release = 0;
constexpr int memory_order_acquire = 0;
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
    friend T atomic_fetch_add_explicit(atomic * a, T const & v, int ) { T r(a->m_value); a->m_value += v; return r; }
    friend T atomic_fetch_sub_explicit(atomic * a, T const & v, int ) { T r(a->m_value); a->m_value -= v; return r; }
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
class this_thread {
public:
    static void sleep_for(chrono::milliseconds const &) {}
    static thread::id get_id() { return 0; }
    static void yield() {}
};
class mutex {
public:
    void lock() {}
    void unlock() {}
};
class recursive_mutex {
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
    ~lock_guard() {}
};
template<typename T> class unique_lock {
public:
    unique_lock(T const &) {}
    ~unique_lock() {}
};
}
#endif

// LEAN_THREAD_PTR macro
#if defined(LEAN_USE_BOOST)
  #include <boost/thread/tss.hpp>
  #define LEAN_THREAD_PTR(T) static boost::thread_specific_ptr<T>
#else
  template<typename T>
  class thread_specific_ptr {
      T * m_ptr;
  public:
      thread_specific_ptr():m_ptr(nullptr) {}
      ~thread_specific_ptr() { if (m_ptr) delete m_ptr; }
      T * get() const { return m_ptr; }
      void reset(T * ptr) { if (m_ptr) delete m_ptr; m_ptr = ptr; }
      T * operator->() const { return m_ptr; }
      T & operator*() { return *m_ptr; }
  };
  #define LEAN_THREAD_PTR(T) static thread_specific_ptr<T> LEAN_THREAD_LOCAL
#endif

#if defined(LEAN_USE_BOOST) && defined(LEAN_MULTI_THREAD)
#define MK_THREAD_LOCAL_GET(T, GETTER_NAME, DEF_VALUE)          \
LEAN_THREAD_PTR(T) GETTER_NAME ## _tlocal;                      \
static T & GETTER_NAME() {                                      \
    if (!(GETTER_NAME ## _tlocal).get())                        \
        (GETTER_NAME ## _tlocal).reset(new T(DEF_VALUE));       \
    return *(GETTER_NAME ## _tlocal);                           \
}

#define MK_THREAD_LOCAL_GET_DEF(T, GETTER_NAME)         \
LEAN_THREAD_PTR(T) GETTER_NAME ## _tlocal;              \
static T & GETTER_NAME() {                              \
    if (!(GETTER_NAME ## _tlocal).get())                \
        (GETTER_NAME ## _tlocal).reset(new T());        \
    return *(GETTER_NAME ## _tlocal);                   \
}
#else
// MK_THREAD_LOCAL_GET_DEF and MK_THREAD_LOCAL_GET when LEAN_USE_BOOST is not defined
// REMARK: LEAN_THREAD_LOCAL is a 'blank' when LEAN_MULTI_THREAD is not defined.
// So, the getter is just returning a reference to a global variable if LEAN_MULTI_THREAD is not defined.
#define MK_THREAD_LOCAL_GET(T, GETTER_NAME, DEF_VALUE) static T & GETTER_NAME() { static T LEAN_THREAD_LOCAL r(DEF_VALUE); return r; }
#define MK_THREAD_LOCAL_GET_DEF(T, GETTER_NAME) static T & GETTER_NAME() { static T LEAN_THREAD_LOCAL r; return r; }
#endif
