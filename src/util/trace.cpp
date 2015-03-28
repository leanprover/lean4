/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

#include <set>
#include <string>
#include <memory>
#include "util/trace.h"

#ifndef LEAN_TRACE_OUT
#define LEAN_TRACE_OUT ".lean_trace"
#endif

namespace lean {

#ifdef LEAN_TRACE
std::ofstream tout(LEAN_TRACE_OUT);
mutex         trace_mutex;
#endif

static std::set<std::string> * g_enabled_trace_tags = nullptr;

void initialize_trace() {
    // lazy initialization
}

void finalize_trace() {
    delete g_enabled_trace_tags;
}

void enable_trace(char const * tag) {
    if (!g_enabled_trace_tags)
        g_enabled_trace_tags = new std::set<std::string>();
    g_enabled_trace_tags->insert(tag);
}

void disable_trace(char const * tag) {
    if (g_enabled_trace_tags)
        g_enabled_trace_tags->erase(tag);
}

bool is_trace_enabled(char const * tag) {
    return g_enabled_trace_tags && g_enabled_trace_tags->find(tag) != g_enabled_trace_tags->end();
}

}
