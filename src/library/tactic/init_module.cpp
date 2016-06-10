/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/assumption_tactic.h"

namespace lean {
void initialize_tactic_module() {
    initialize_tactic_state();
    initialize_intro_tactic();
    initialize_assumption_tactic();
}
void finalize_tactic_module() {
    finalize_assumption_tactic();
    finalize_intro_tactic();
    finalize_tactic_state();
}
}
