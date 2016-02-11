/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/ascii.h"
#include "util/debug.h"
#include "util/serializer.h"
#include "util/name.h"
#include "util/lean_path.h"
#include "util/thread.h"
#include "util/memory_pool.h"

namespace lean {
void initialize_util_module() {
    initialize_debug();
    initialize_serializer();
    initialize_thread();
    initialize_ascii();
    initialize_name();
    initialize_lean_path();
}
void finalize_util_module() {
    finalize_lean_path();
    finalize_name();
    finalize_ascii();
    finalize_thread();
    finalize_serializer();
    finalize_debug();
}
}
