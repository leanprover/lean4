/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/ascii.h"
#include "util/debug.h"
#include "util/trace.h"
#include "util/serializer.h"
#include "util/thread_script_state.h"
#include "util/script_state.h"
#include "util/name.h"
#include "util/name_generator.h"
#include "util/lean_path.h"
#include "util/thread.h"
#include "util/memory_pool.h"

namespace lean {
void initialize_util_module() {
    initialize_debug();
    initialize_trace();
    initialize_serializer();
    initialize_thread();
    initialize_ascii();
    initialize_thread_script_state();
    initialize_script_state();
    initialize_name();
    initialize_name_generator();
    initialize_lean_path();
}
void finalize_util_module() {
    finalize_lean_path();
    finalize_name_generator();
    finalize_name();
    finalize_script_state();
    finalize_thread_script_state();
    finalize_ascii();
    finalize_thread();
    finalize_serializer();
    finalize_trace();
    finalize_debug();
}
}
