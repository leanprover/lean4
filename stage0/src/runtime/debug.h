/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <typeinfo>
#include "runtime/exception.h"

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#ifdef LEAN_DEBUG
#define DEBUG_CODE(CODE) CODE
#else
#define DEBUG_CODE(CODE)
#endif

#define lean_unreachable() { DEBUG_CODE({lean::notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); lean::invoke_debugger();}) throw lean::unreachable_reached(); }

#ifdef LEAN_DEBUG
#define lean_verify(COND) if (LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }
#else
#define lean_verify(COND) (COND)
#endif

#define lean_assert(COND) DEBUG_CODE({if (LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }})
#define lean_cond_assert(TAG, COND) DEBUG_CODE({if (lean::is_debug_enabled(TAG) && LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }})
#define lean_always_assert(COND) { if (LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean_unreachable(); } }

namespace lean {
void initialize_debug();
void finalize_debug();
LEAN_EXPORT void notify_assertion_violation(char const * file_name, int line, char const * condition);
LEAN_EXPORT void enable_debug(char const * tag);
LEAN_EXPORT void disable_debug(char const * tag);
LEAN_EXPORT bool is_debug_enabled(char const * tag);
LEAN_EXPORT void invoke_debugger();
LEAN_EXPORT bool has_violations();
LEAN_EXPORT void enable_debug_dialog(bool flag);
// LCOV_EXCL_START
/** \brief Exception used to sign that unreachable code was reached */
class unreachable_reached : public exception {
public:
    unreachable_reached() {}
    virtual ~unreachable_reached() noexcept {}
    virtual char const * what() const noexcept { return "'unreachable' code was reached"; }
};
// LCOV_EXCL_STOP
}
