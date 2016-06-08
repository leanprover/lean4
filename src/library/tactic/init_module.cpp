/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"

namespace lean {
void initialize_tactic_module() {
    initialize_tactic_state();
}
void finalize_tactic_module() {
    finalize_tactic_state();
}
}
