/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lean/runtime/alloc.h>
#include <lean/runtime/debug.h>
#include <lean/runtime/serializer.h>
#include <lean/runtime/thread.h>
#include <lean/runtime/object.h>
#include <lean/runtime/io.h>
#include <lean/runtime/stack_overflow.h>

namespace lean {
extern "C" void lean_initialize_runtime_module() {
    initialize_alloc();
    initialize_debug();
    initialize_object();
    initialize_io();
    initialize_serializer();
    initialize_thread();
    initialize_stack_overflow();
}
void initialize_runtime_module() {
    lean_initialize_runtime_module();
}
void finalize_runtime_module() {
    finalize_stack_overflow();
    finalize_thread();
    finalize_serializer();
    finalize_io();
    finalize_object();
    finalize_debug();
    finalize_alloc();
}
}
