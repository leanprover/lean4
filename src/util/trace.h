/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

#ifdef LEAN_TRACE
#include "util/thread.h"
#include <fstream>
namespace lean {
extern std::ofstream tout;
extern mutex         trace_mutex;
}
#define TRACE_CODE(CODE) { lock_guard<mutex> _lean_trace_lock_(lean::trace_mutex); CODE }
#else
#define TRACE_CODE(CODE)
#endif

#define lean_trace(TAG, CODE) TRACE_CODE(if (lean::is_trace_enabled(TAG)) { lean::tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"; CODE lean::tout << "------------------------------------------------\n"; lean::tout.flush(); })

#define lean_simple_trace(TAG, CODE) TRACE_CODE(if (lean::is_trace_enabled(TAG)) { CODE lean::tout.flush(); })

#define lean_cond_trace(TAG, COND, CODE) TRACE_CODE(if (lean::is_trace_enabled(TAG) && (COND)) { lean::tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"; CODE lean::tout << "------------------------------------------------\n"; lean::tout.flush(); })

namespace lean {
void enable_trace(char const * tag);
void disable_trace(char const * tag);
bool is_trace_enabled(char const * tag);
void initialize_trace();
void finalize_trace();
}
