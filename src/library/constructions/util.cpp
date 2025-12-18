/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/constants.h"

namespace lean {
static name * g_constructions_fresh = nullptr;

name_generator mk_constructions_name_generator() {
    return name_generator(*g_constructions_fresh);
}

void initialize_constructions_util() {
    g_constructions_fresh = new name("_cnstr_fresh");
    mark_persistent(g_constructions_fresh->raw());
    register_name_generator_prefix(*g_constructions_fresh);
}

void finalize_constructions_util() {
    delete g_constructions_fresh;
}
}
