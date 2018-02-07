/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"

namespace lean {
static name * g_constructions = nullptr;

name_generator mk_constructions_name_generator() {
    return name_generator(*g_constructions);
}

void initialize_constructions_util() {
    g_constructions = new name("_constrs");
}

void finalize_constructions_util() {
    delete g_constructions;
}
}
