/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/proof_state.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/rename_tactic.h"
#include "library/tactic/intros_tactic.h"
#include "library/tactic/trace_tactic.h"
#include "library/tactic/exact_tactic.h"
#include "library/tactic/unfold_tactic.h"
#include "library/tactic/generalize_tactic.h"

namespace lean {
void initialize_tactic_module() {
    initialize_proof_state();
    initialize_expr_to_tactic();
    initialize_apply_tactic();
    initialize_rename_tactic();
    initialize_intros_tactic();
    initialize_trace_tactic();
    initialize_exact_tactic();
    initialize_unfold_tactic();
    initialize_generalize_tactic();
}

void finalize_tactic_module() {
    finalize_generalize_tactic();
    finalize_unfold_tactic();
    finalize_exact_tactic();
    finalize_trace_tactic();
    finalize_intros_tactic();
    finalize_rename_tactic();
    finalize_apply_tactic();
    finalize_expr_to_tactic();
    finalize_proof_state();
}
}
