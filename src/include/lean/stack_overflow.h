/*
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#ifndef LEAN_WINDOWS
#include <csignal>
#endif

namespace lean {
class stack_guard {
#ifndef LEAN_WINDOWS
    // We need a separate signal stack since we can't use the overflowed stack
    stack_t m_signal_stack;
#endif
public:
    stack_guard();
    ~stack_guard();
};

void initialize_stack_overflow();
void finalize_stack_overflow();
}
