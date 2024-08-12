/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constructions/init_module.h"
#include "library/constructions/projection.h"
#include "library/constructions/util.h"

namespace lean{
void initialize_constructions_module() {
    initialize_constructions_util();
    initialize_def_projection();
}

void finalize_constructions_module() {
    finalize_def_projection();
    finalize_constructions_util();
}
}
