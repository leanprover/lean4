/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/expr.h"
#include "library/blast/branch.h"
#include "library/blast/blast.h"
#include "library/blast/blast_tactic.h"
#include "library/blast/simplifier.h"

namespace lean {
void initialize_blast_module() {
    blast::initialize_expr();
    blast::initialize_branch();
    initialize_blast();
    blast::initialize_simplifier();
    initialize_blast_tactic();
}
void finalize_blast_module() {
    finalize_blast_tactic();
    blast::finalize_simplifier();
    finalize_blast();
    blast::finalize_branch();
    blast::finalize_expr();
}
}
