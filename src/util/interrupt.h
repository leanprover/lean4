/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <atomic>
#include <thread>
#include <utility>

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
bool interrupted();

/**
   \brief Throw an interrupt exception if the (interrupt) flag is set.
*/
void check_interrupt();

/**
   \brief Thread that provides a method for setting its interrupt flag.
*/
class interruptible_thread {
    std::atomic<std::atomic_bool*> m_flag_addr;
    std::thread                    m_thread;
    static std::atomic_bool *      get_flag_addr();
public:
    template<typename Function, typename... Args>
    interruptible_thread(Function && fun, Args &&... args):
        m_flag_addr(nullptr),
        m_thread(
            [&](Function&& fun, Args&&... args) {
                m_flag_addr.store(get_flag_addr());
                fun(std::forward<Args>(args)...);
            },
            std::forward<Function>(fun),
            std::forward<Args>(args)...)
        {}

    /**
       \brief Return true iff an interrupt request has been made to the current thread.
    */
    bool interrupted() const;
    /**
       \brief Send a interrupt request to the current thread. Return
       true iff the request has been successfully performed.
    */
    bool request_interrupt();

    void join();
    bool joinable();
};
}
