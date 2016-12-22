/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/congruence/congruence_closure.h"

namespace lean {
void initialize_congruence_module() {
    initialize_congruence_closure();
}
void finalize_congruence_module() {
    finalize_congruence_module();
}
}
