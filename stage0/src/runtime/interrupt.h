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

/**
   \brief Throw an interrupted exception if the current task is marked cancelled.
*/
void check_interrupted();

/**
   \brief Check system resources: stack, memory, heartbeat, interrupt flag.

   `do_check_interrupted` should only be set to `true` in places where a C++ exception
   is caught and would not bring down the entire process as interruption
   should not be a fatal error.
*/
void check_system(char const * component_name, bool do_check_interrupted = false);

constexpr unsigned g_small_sleep = 10;

/**
   \brief Put the current thread to sleep for \c ms milliseconds.

   \remark check_interrupted is invoked every \c step_ms milliseconds;
*/
void sleep_for(unsigned ms, unsigned step_ms = g_small_sleep);
inline void sleep_for(chrono::milliseconds const & ms) { sleep_for(ms.count(), 10); }
}
