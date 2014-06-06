/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
namespace lean {
/**
    \brief Execute the given piece of code in all global/system script_state objects.

    \remark The code fragments are saved. If a new thread needs to create a new
    script_state object, all code blocks are executed.

    \remark System code should be installed when Lean is started.
*/
void system_dostring(char const * code);
/**
   \brief Retrieve a script_state object for the current thread.
   The thread has exclusive access until the thread is destroyed,
   or the method \c release_thread_script_state is invoked.

   \remark For performance reasons global script_state objects
   are recycled. So, users should not delete/redefine functions
   defined using #system_dostring. So, side-effects are discouraged.
*/
script_state get_thread_script_state();
/**
   \brief Put the thread script_state back on the state pool,
   and available for other threads.
*/
void release_thread_script_state();
}
