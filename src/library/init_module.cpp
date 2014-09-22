/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/unifier.h"

namespace lean {
void initialize_library_module() {
    initialize_unifier();
}

void finalize_library_module() {
    finalize_unifier();
}
}
