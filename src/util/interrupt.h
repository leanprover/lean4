/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/thread.h"
#include "util/stackinfo.h"
#include "util/exception.h"

namespace lean {
/**
   \brief Mark flag for interrupting current thread.
*/
void request_interrupt();
/**
   \brief Reset (interrupt) flag for current thread.
*/
void reset_interrupt();

/**
   \brief Return true iff the current thread was marked for interruption.
*/
bool interrupt_requested();

/**
   \brief Throw an interrupted exception if the (interrupt) flag is set.
*/
void check_interrupted();

/**
   \brief Check system resources: stack, memory, interrupt flag.
*/
void check_system(char const * component_name);

constexpr unsigned g_small_sleep = 50;

/**
   \brief Put the current thread to sleep for \c ms milliseconds.

   \remark check_interrupted is invoked every \c step_ms milliseconds;
*/
void sleep_for(unsigned ms, unsigned step_ms = g_small_sleep);

/**
   \brief Thread that provides a method for setting its interrupt flag.
*/
class interruptible_thread {
public:
    #if !defined(LEAN_USE_BOOST)
    template<typename Function, typename... Args>
    interruptible_thread(Function && fun, Args &&... args):
        m_flag_addr(nullptr),
        m_thread(
            [&](Function&& fun, Args&&... args) {
                m_flag_addr.store(get_flag_addr());
                save_stack_info(false);
                fun(std::forward<Args>(args)...);
                m_flag_addr.store(&m_dummy_addr); // see comment before m_dummy_addr
                run_thread_finalizers();
                run_post_thread_finalizers();
            },
            std::forward<Function>(fun),
            std::forward<Args>(args)...)
        {}
    #else
    // Simpler version that works with Boost, and set stack size
private:
    std::function<void()> m_fun;
    static void execute(interruptible_thread * _this) {
        _this->m_flag_addr.store(get_flag_addr());
        save_stack_info(false);
        _this->m_fun();
        _this->m_flag_addr.store(&(_this->m_dummy_addr)); // see comment before m_dummy_addr
        run_thread_finalizers();
        run_post_thread_finalizers();
    }
public:
    template<typename Function>
    interruptible_thread(Function && fun):m_fun(fun), m_flag_addr(nullptr), m_thread(get_thread_attributes(), boost::bind(execute, this)) {}
    #endif

    /**
       \brief Return true iff an interrupt request has been made to the current thread.
    */
    bool interrupted() const;
    /**
       \brief Send a interrupt request to the current thread. Return
       true iff the request has been successfully performed.

       \remark The main thread may have to wait the interrupt flag of this thread to
       be initialized. If the flag was not initialized, then the main thread will be put
       to sleep for \c try_ms milliseconds until it tries to set the flag again.
    */
    void request_interrupt(unsigned try_ms = g_small_sleep);

    void join();
    bool joinable();
private:
    atomic<atomic_bool*> m_flag_addr;
    /*
      The following auxiliary field is used to workaround a nasty bug
      that occurs in some platforms. On cygwin, it seems that the
      thread local storage is deleted before m_thread is destructed.
      Then, the main thread may corrupt memory if it invokes
      request_interrupt after the child thread referenced by m_thread
      has terminated.

      The method request_interrupt access the child
      thread local storage pointed by m_flag_addr.

      To avoid this bug, we use a simple hack, we reset m_flag_addr to
      m_dummy_addr before terminating the execution of the child
      thread.
    */
    atomic_bool           m_dummy_addr;
    thread                m_thread;
    static atomic_bool *  get_flag_addr();
};

#if !defined(LEAN_MULTI_THREAD)
inline void check_threadsafe() {
    throw exception("Lean was compiled without support for multi-threading");
}
#else
inline void check_threadsafe() {}
#endif
}
