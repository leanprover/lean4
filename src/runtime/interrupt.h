/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "runtime/thread.h"
#include "runtime/stackinfo.h"
#include "runtime/exception.h"
#include "runtime/flet.h"

namespace lean {
/** \brief Increment thread local counter for approximating elapsed time. */
void inc_heartbeat();

/** \brief Reset thread local counter for approximating elapsed time. */
void reset_heartbeat();

/* Update the current heartbeat */
class scope_heartbeat : flet<size_t> {
public:
    scope_heartbeat(size_t curr);
};

/** \brief Threshold on the number of heartbeats. check_system will throw
    an exception if a thread exceeds the limit. The default is unlimited.
    The limit is checked in the check_system API.

    This is a thread local value. The class lthread uses the
    maximum of the parent thread. */
void set_max_heartbeat(size_t max);
void set_max_heartbeat_thousands(unsigned max);
size_t get_max_heartbeat();

/* Update the thread local max heartbeat */
class scope_max_heartbeat : flet<size_t> {
public:
    scope_max_heartbeat(size_t max);
};

void check_heartbeat();

struct scoped_interrupt_flag : flet<atomic_bool *> {
    scoped_interrupt_flag(atomic_bool *); // NOLINT
};

/**
   \brief Throw an interrupted exception if the (interrupt) flag is set.
*/
void check_interrupted();

/**
   \brief Check system resources: stack, memory, heartbeat, interrupt flag.
*/
void check_system(char const * component_name);

constexpr unsigned g_small_sleep = 10;

/**
   \brief Put the current thread to sleep for \c ms milliseconds.

   \remark check_interrupted is invoked every \c step_ms milliseconds;
*/
void sleep_for(unsigned ms, unsigned step_ms = g_small_sleep);
inline void sleep_for(chrono::milliseconds const & ms) { sleep_for(ms.count(), 10); }

/**
   \brief Thread that provides a method for setting its interrupt flag.
*/
class interruptible_thread {
public:
    template<typename Function>
    interruptible_thread(Function && fun):
        m_thread([&, fun]() {
                save_stack_info(false);
                scoped_interrupt_flag scope_int_flag(&m_flag);
                fun();
            })
        {}

    /**
       \brief Return true iff an interrupt request has been made to the current thread.
    */
    bool interrupted() const;
    /**
       \brief Send a interrupt request to the current thread. Return
       true iff the request has been successfully performed.
    */
    void request_interrupt();

    void join();
private:
    atomic_bool m_flag;
    lthread m_thread;
};

#if !defined(LEAN_MULTI_THREAD)
inline void check_threadsafe() {
    throw exception("Lean was compiled without support for multi-threading");
}
#else
inline void check_threadsafe() {}
#endif
}
