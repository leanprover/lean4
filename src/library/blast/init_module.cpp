/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/expr.h"
#include "library/blast/blast.h"
#include "library/blast/blast_tactic.h"

namespace lean {
void initialize_blast_module() {
    blast::initialize_expr();
    initialize_blast();
    initialize_blast_tactic();
}
void finalize_blast_module() {
    blast::finalize_expr();
    finalize_blast();
    finalize_blast_tactic();
}
}
