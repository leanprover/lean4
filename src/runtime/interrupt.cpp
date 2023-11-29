/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/exception.h"
#include "runtime/memory.h"
#include "lean/lean.h"

namespace lean {
LEAN_THREAD_VALUE(size_t, g_max_heartbeat, 0);
LEAN_THREAD_VALUE(size_t, g_heartbeat, 0);

void inc_heartbeat() { g_heartbeat++; }

void reset_heartbeat() { g_heartbeat = 0; }

void set_max_heartbeat(size_t max) { g_max_heartbeat = max; }

size_t get_max_heartbeat() { return g_max_heartbeat; }

void set_max_heartbeat_thousands(unsigned max) { g_max_heartbeat = static_cast<size_t>(max) * 1000; }

scope_heartbeat::scope_heartbeat(size_t max):flet<size_t>(g_heartbeat, max) {}
scope_max_heartbeat::scope_max_heartbeat(size_t max):flet<size_t>(g_max_heartbeat, max) {}

// separate definition to allow breakpoint in debugger
void throw_heartbeat_exception() {
    throw heartbeat_exception();
}

void check_heartbeat() {
    inc_heartbeat();
    if (g_max_heartbeat > 0 && g_heartbeat > g_max_heartbeat)
        throw_heartbeat_exception();
}

void check_interrupted() {
    if (lean_io_check_canceled_core() && !std::uncaught_exception()) {
        throw interrupted();
    }
}

void check_system(char const * component_name, bool do_check_interrupted) {
    check_stack(component_name);
    check_memory(component_name);
    if (do_check_interrupted)
        check_interrupted();
    check_heartbeat();
}

void sleep_for(unsigned ms, unsigned step_ms) {
    if (step_ms == 0)
        step_ms = 1;
    unsigned rounds = ms / step_ms;
    chrono::milliseconds c(step_ms);
    chrono::milliseconds r(ms % step_ms);
    for (unsigned i = 0; i < rounds; i++) {
        this_thread::sleep_for(c);
        check_interrupted();
    }
    this_thread::sleep_for(r);
    check_interrupted();
}
}
