/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/goal.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/rename_tactic.h"
#include "library/tactic/intros_tactic.h"
#include "library/tactic/trace_tactic.h"
#include "library/tactic/exact_tactic.h"
#include "library/tactic/generalize_tactic.h"
#include "library/tactic/whnf_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/inversion_tactic.h"
#include "library/tactic/assert_tactic.h"
#include "library/tactic/class_instance_synth.h"
#include "library/tactic/rewrite_tactic.h"
#include "library/tactic/change_tactic.h"
#include "library/tactic/check_expr_tactic.h"
#include "library/tactic/let_tactic.h"
#include "library/tactic/contradiction_tactic.h"
#include "library/tactic/exfalso_tactic.h"
#include "library/tactic/constructor_tactic.h"
#include "library/tactic/injection_tactic.h"
#include "library/tactic/congruence_tactic.h"
#include "library/tactic/equivalence_tactics.h"

namespace lean {
void initialize_tactic_module() {
    initialize_goal();
    initialize_proof_state();
    initialize_expr_to_tactic();
    initialize_apply_tactic();
    initialize_rename_tactic();
    initialize_intros_tactic();
    initialize_trace_tactic();
    initialize_exact_tactic();
    initialize_generalize_tactic();
    initialize_whnf_tactic();
    initialize_clear_tactic();
    initialize_revert_tactic();
    initialize_inversion_tactic();
    initialize_assert_tactic();
    initialize_class_instance_elaborator();
    initialize_rewrite_tactic();
    initialize_change_tactic();
    initialize_check_expr_tactic();
    initialize_let_tactic();
    initialize_contradiction_tactic();
    initialize_exfalso_tactic();
    initialize_constructor_tactic();
    initialize_injection_tactic();
    initialize_congruence_tactic();
    initialize_equivalence_tactics();
}

void finalize_tactic_module() {
    finalize_equivalence_tactics();
    finalize_congruence_tactic();
    finalize_injection_tactic();
    finalize_constructor_tactic();
    finalize_exfalso_tactic();
    finalize_contradiction_tactic();
    finalize_let_tactic();
    finalize_check_expr_tactic();
    finalize_change_tactic();
    finalize_rewrite_tactic();
    finalize_class_instance_elaborator();
    finalize_assert_tactic();
    finalize_inversion_tactic();
    finalize_revert_tactic();
    finalize_clear_tactic();
    finalize_whnf_tactic();
    finalize_generalize_tactic();
    finalize_exact_tactic();
    finalize_trace_tactic();
    finalize_intros_tactic();
    finalize_rename_tactic();
    finalize_apply_tactic();
    finalize_expr_to_tactic();
    finalize_proof_state();
    finalize_goal();
}
}
