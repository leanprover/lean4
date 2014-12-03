/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/definitional/util.h"

namespace lean{
void initialize_definitional_module() {
    initialize_definitional_util();
}

void finalize_definitional_module() {
    finalize_definitional_util();
}
}
