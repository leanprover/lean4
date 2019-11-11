/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/init_module.h"
#include "util/ascii.h"
#include "util/name.h"
#include "util/fresh_name.h"
#include "util/name_generator.h"
#include "util/options.h"
#include "util/option_declarations.h"
#include "util/format.h"

namespace lean {
void initialize_util_module() {
    initialize_runtime_module();
    initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_fresh_name();
    initialize_option_declarations();
    initialize_options();
    initialize_format();
}
void finalize_util_module() {
    finalize_format();
    finalize_options();
    finalize_option_declarations();
    finalize_fresh_name();
    finalize_name_generator();
    finalize_name();
    finalize_ascii();
    finalize_runtime_module();
}
}
