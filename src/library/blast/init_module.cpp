/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/blast.h"
#include "library/blast/blast_tactic.h"
#include "library/blast/simplifier.h"
#include "library/blast/options.h"

namespace lean {
void initialize_blast_module() {
    blast::initialize_options();
    blast::initialize_expr();
    blast::initialize_state();
    initialize_blast();
    blast::initialize_simplifier();
    initialize_blast_tactic();
}
void finalize_blast_module() {
    finalize_blast_tactic();
    blast::finalize_simplifier();
    finalize_blast();
    blast::finalize_state();
    blast::finalize_expr();
    blast::finalize_options();
}
}
