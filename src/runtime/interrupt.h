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
LEAN_EXPORT void inc_heartbeat();

/** \brief Reset thread local counter for approximating elapsed time. */
LEAN_EXPORT void reset_heartbeat();

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
LEAN_EXPORT void set_max_heartbeat(size_t max);
LEAN_EXPORT void set_max_heartbeat_thousands(unsigned max);
LEAN_EXPORT size_t get_max_heartbeat();

/* Update the thread local max heartbeat */
class LEAN_EXPORT scope_max_heartbeat : flet<size_t> {
public:
    LEAN_EXPORT scope_max_heartbeat(size_t max);
};

LEAN_EXPORT void check_heartbeat();

/* Update the thread local `IO.CancelToken` (`nullptr` if unset) */
class LEAN_EXPORT scope_cancel_tk : flet<lean_object *> {
public:
    LEAN_EXPORT scope_cancel_tk(lean_object *);
};

/**
   \brief Throw an interrupted exception if the current thread's cancel token is set.
*/
LEAN_EXPORT void check_interrupted();

/**
   \brief Check system resources: stack, memory, and (if `do_check_interrupted` is true) heartbeat
   limit and interrupt flag.

   `do_check_interrupted` should only be set to `true` in places where a C++ exception is caught and
   would not bring down the entire process as interruption (via heartbeat limit or flag) should not
   be a fatal error.
*/
LEAN_EXPORT void check_system(char const * component_name, bool do_check_interrupted = false);

constexpr unsigned g_small_sleep = 10;

/**
   \brief Put the current thread to sleep for \c ms milliseconds.

   \remark check_interrupted is invoked every \c step_ms milliseconds;
*/
LEAN_EXPORT void sleep_for(unsigned ms, unsigned step_ms = g_small_sleep);
LEAN_EXPORT inline void sleep_for(chrono::milliseconds const & ms) { sleep_for(ms.count(), 10); }
}
