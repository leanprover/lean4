/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "util/interrupt.h"
#include "util/exception.h"
#include "util/memory.h"

namespace lean {
MK_THREAD_LOCAL_GET(atomic_bool, get_g_interrupt, false);

void request_interrupt() {
    get_g_interrupt().store(true);
}

void reset_interrupt() {
    get_g_interrupt().store(false);
}

bool interrupt_requested() {
    return get_g_interrupt().load();
}

void check_interrupted() {
    if (interrupt_requested()) {
        reset_interrupt();
        throw interrupted();
    }
}

void check_system(char const * component_name) {
    check_stack(component_name);
    check_memory(component_name);
    check_interrupted();
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

atomic_bool * interruptible_thread::get_flag_addr() {
    return &get_g_interrupt();
}

bool interruptible_thread::interrupted() const {
    atomic_bool * f = m_flag_addr.load();
    if (f == nullptr)
        return false;
    return f->load();
}

void interruptible_thread::request_interrupt(unsigned try_ms) {
    while (true) {
        atomic_bool * f = m_flag_addr.load();
        if (f != nullptr) {
            f->store(true);
            return;
        }
        this_thread::sleep_for(chrono::milliseconds(try_ms));
        check_interrupted();
    }
}

void interruptible_thread::join() {
    m_thread.join();
}

bool interruptible_thread::joinable() {
    return m_thread.joinable();
}
}
