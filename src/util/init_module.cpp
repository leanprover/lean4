/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/ascii.h"
#include "util/debug.h"
#include "util/serializer.h"
#include "util/name.h"
#include "util/thread.h"
#include "util/memory_pool.h"
#include "util/fresh_name.h"
#include "util/name_generator.h"

namespace lean {
void initialize_util_module() {
    initialize_debug();
    initialize_serializer();
    initialize_thread();
    initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_fresh_name();
}
void finalize_util_module() {
    finalize_fresh_name();
    finalize_name_generator();
    finalize_name();
    finalize_ascii();
    finalize_thread();
    finalize_serializer();
    finalize_debug();
}
}
