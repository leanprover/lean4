/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/alloc.h"
#include "runtime/debug.h"
#include "runtime/serializer.h"
#include "runtime/thread.h"
#include "runtime/object.h"
namespace lean {
void initialize_runtime_module() {
    initialize_alloc();
    initialize_debug();
    initialize_object();
    initialize_serializer();
    initialize_thread();
}
void finalize_runtime_module() {
    finalize_thread();
    finalize_serializer();
    finalize_object();
    finalize_debug();
    finalize_alloc();
}
}
