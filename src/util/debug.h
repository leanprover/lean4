/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#pragma once

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#ifdef LEAN_DEBUG
#define DEBUG_CODE(CODE) CODE
#else
#define DEBUG_CODE(CODE) 
#endif

#define lean_assert(COND) DEBUG_CODE({if (!(COND)) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }})
#define lean_cond_assert(TAG, COND) DEBUG_CODE({if (lean::is_debug_enabled(TAG) && !(COND)) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }})

#if __has_builtin(__builtin_unreachable)
#define lean_unreachable() __builtin_unreachable()
#else
#define lean_unreachable() DEBUG_CODE({lean::notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); lean::invoke_debugger();})
#endif

#ifdef LEAN_DEBUG
#define lean_verify(COND) if (!(COND)) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }
#else
#define lean_verify(COND) (COND)
#endif

namespace lean {

void abort_on_violation(bool flag); 
void notify_assertion_violation(char const * file_name, int line, char const * condition);
void enable_debug(char const * tag);
void disable_debug(char const * tag);
bool is_debug_enabled(char const * tag);
void invoke_debugger();

}
