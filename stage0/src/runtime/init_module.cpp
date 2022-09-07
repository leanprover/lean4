/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/thread.h"
#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/stack_overflow.h"
#include "runtime/process.h"
#include "runtime/mutex.h"

namespace lean {
extern "C" LEAN_EXPORT void lean_initialize_runtime_module() {
    initialize_alloc();
    initialize_debug();
    initialize_object();
    initialize_io();
    initialize_thread();
    initialize_mutex();
    initialize_process();
    initialize_stack_overflow();
}
void initialize_runtime_module() {
    lean_initialize_runtime_module();
}
void finalize_runtime_module() {
    finalize_stack_overflow();
    finalize_process();
    finalize_mutex();
    finalize_thread();
    finalize_io();
    finalize_object();
    finalize_debug();
    finalize_alloc();
}
}
