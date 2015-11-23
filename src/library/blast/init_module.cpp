/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/blast.h"
#include "library/blast/blast_tactic.h"
#include "library/blast/options.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/recursor_action.h"
#include "library/blast/assert_cc_action.h"
#include "library/blast/simplifier/init_module.h"
#include "library/blast/backward/init_module.h"
#include "library/blast/forward/init_module.h"
#include "library/blast/unit/init_module.h"

namespace lean {
void initialize_blast_module() {
    blast::initialize_options();
    blast::initialize_expr();
    blast::initialize_state();
    initialize_blast();
    blast::initialize_simplifier_module();
    blast::initialize_backward_module();
    blast::initialize_forward_module();
    blast::initialize_unit_module();
    initialize_blast_tactic();
    blast::initialize_recursor_action();
    blast::initialize_assert_cc_action();
    blast::initialize_congruence_closure();
}
void finalize_blast_module() {
    blast::finalize_congruence_closure();
    blast::finalize_assert_cc_action();
    blast::finalize_recursor_action();
    finalize_blast_tactic();
    blast::finalize_unit_module();
    blast::finalize_forward_module();
    blast::finalize_backward_module();
    blast::finalize_simplifier_module();
    finalize_blast();
    blast::finalize_state();
    blast::finalize_expr();
    blast::finalize_options();
}
}
