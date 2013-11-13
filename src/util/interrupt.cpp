/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/exception.h"

namespace lean {
static thread_local std::atomic_bool g_interrupt;

void request_interrupt() {
    g_interrupt.store(true);
}

void reset_interrupt() {
    g_interrupt.store(false);
}

bool interrupt_requested() {
    return g_interrupt.load();
}

void check_interrupted() {
    if (interrupt_requested())
        throw interrupted();
}

std::atomic_bool * interruptible_thread::get_flag_addr() {
    return &g_interrupt;
}

bool interruptible_thread::interrupted() const {
    std::atomic_bool * f = m_flag_addr.load();
    if (f == nullptr)
        return false;
    return f->load();
}

bool interruptible_thread::request_interrupt() {
    std::atomic_bool * f = m_flag_addr.load();
    if (f == nullptr)
        return false;
    f->store(true);
    return true;
}

void interruptible_thread::join() {
    m_thread.join();
}

bool interruptible_thread::joinable() {
    return m_thread.joinable();
}
}
