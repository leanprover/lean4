/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/ascii.h"
#include "util/debug.h"
#include "util/trace.h"
#include "util/serializer.h"
#include "util/name.h"
#include "util/lean_path.h"
#include "util/thread.h"

namespace lean {
void initialize_util_module() {
    initialize_debug();
    initialize_trace();
    initialize_thread();
    initialize_ascii();
    initialize_lean_path();
    initialize_serializer();
    initialize_name();
}
void finalize_util_module() {
    finalize_name();
    finalize_serializer();
    finalize_lean_path();
    finalize_ascii();
    finalize_thread();
    finalize_trace();
    finalize_debug();
}
}
