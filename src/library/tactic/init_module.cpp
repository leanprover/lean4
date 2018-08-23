/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/subst_tactic.h"
#include "library/tactic/induction_tactic.h"
#include "library/tactic/cases_tactic.h"

namespace lean {
void initialize_tactic_module() {
    initialize_tactic_state();
    initialize_intro_tactic();
    initialize_revert_tactic();
    initialize_clear_tactic();
    initialize_subst_tactic();
    initialize_induction_tactic();
    initialize_cases_tactic();
}
void finalize_tactic_module() {
    finalize_cases_tactic();
    finalize_induction_tactic();
    finalize_subst_tactic();
    finalize_clear_tactic();
    finalize_revert_tactic();
    finalize_intro_tactic();
    finalize_tactic_state();
}
}
