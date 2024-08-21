/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/init_module.h"
#include "runtime/init_module.h"
#include "util/ascii.h"
#include "util/name.h"
#include "util/name_generator.h"
#include "util/options.h"

namespace lean {
void initialize_util_module() {
    initialize_runtime_module();
    initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_options();
}
void finalize_util_module() {
    finalize_options();
    finalize_name_generator();
    finalize_name();
    finalize_ascii();
    finalize_runtime_module();
}
}
