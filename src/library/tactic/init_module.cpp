/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/kabstract.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/rename_tactic.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/app_builder_tactics.h"
#include "library/tactic/subst_tactic.h"
#include "library/tactic/exact_tactic.h"
#include "library/tactic/change_tactic.h"
#include "library/tactic/assert_tactic.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/fun_info_tactics.h"
#include "library/tactic/congr_lemma_tactics.h"
#include "library/tactic/match_tactic.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/induction_tactic.h"
#include "library/tactic/cases_tactic.h"
#include "library/tactic/generalize_tactic.h"
#include "library/tactic/rewrite_tactic.h"
#include "library/tactic/unfold_tactic.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/user_attribute.h"
#include "library/tactic/defeq_simplifier.h"
#include "library/tactic/eval.h"
#include "library/tactic/simp_lemmas_tactics.h"
#include "library/tactic/simplifier/init_module.h"
#include "library/tactic/backward/init_module.h"

namespace lean {
void initialize_tactic_module() {
    initialize_kabstract();
    initialize_tactic_state();
    initialize_intro_tactic();
    initialize_revert_tactic();
    initialize_rename_tactic();
    initialize_clear_tactic();
    initialize_app_builder_tactics();
    initialize_subst_tactic();
    initialize_exact_tactic();
    initialize_change_tactic();
    initialize_assert_tactic();
    initialize_apply_tactic();
    initialize_fun_info_tactics();
    initialize_congr_lemma_tactics();
    initialize_match_tactic();
    initialize_ac_tactics();
    initialize_induction_tactic();
    initialize_cases_tactic();
    initialize_generalize_tactic();
    initialize_rewrite_tactic();
    initialize_unfold_tactic();
    initialize_defeq_simplifier();
    initialize_simplifier_module();
    initialize_backward_module();
    initialize_elaborate();
    initialize_user_attribute();
    initialize_eval();
    initialize_simp_lemmas_tactics();
}
void finalize_tactic_module() {
    finalize_simp_lemmas_tactics();
    finalize_eval();
    finalize_user_attribute();
    finalize_elaborate();
    finalize_backward_module();
    finalize_simplifier_module();
    finalize_defeq_simplifier();
    finalize_unfold_tactic();
    finalize_rewrite_tactic();
    finalize_generalize_tactic();
    finalize_cases_tactic();
    finalize_induction_tactic();
    finalize_ac_tactics();
    finalize_match_tactic();
    finalize_congr_lemma_tactics();
    finalize_fun_info_tactics();
    finalize_apply_tactic();
    finalize_assert_tactic();
    finalize_change_tactic();
    finalize_exact_tactic();
    finalize_subst_tactic();
    finalize_app_builder_tactics();
    finalize_clear_tactic();
    finalize_rename_tactic();
    finalize_revert_tactic();
    finalize_intro_tactic();
    finalize_tactic_state();
    finalize_kabstract();
}
}
