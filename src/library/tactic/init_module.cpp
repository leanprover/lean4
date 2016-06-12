/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/assumption_tactic.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/rename_tactic.h"
#include "library/tactic/clear_tactic.h"

namespace lean {
void initialize_tactic_module() {
    initialize_tactic_state();
    initialize_intro_tactic();
    initialize_assumption_tactic();
    initialize_revert_tactic();
    initialize_rename_tactic();
    initialize_clear_tactic();
}
void finalize_tactic_module() {
    finalize_clear_tactic();
    finalize_rename_tactic();
    finalize_revert_tactic();
    finalize_assumption_tactic();
    finalize_intro_tactic();
    finalize_tactic_state();
}
}
