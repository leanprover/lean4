/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/smt/util.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/hinst_lemmas.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/theory_ac.h"

namespace lean {
void initialize_smt_module() {
    initialize_smt_util();
    initialize_congruence_closure();
    initialize_congruence_tactics();
    initialize_hinst_lemmas();
    initialize_ematch();
    initialize_theory_ac();
}

void finalize_smt_module() {
    finalize_theory_ac();
    finalize_ematch();
    finalize_hinst_lemmas();
    finalize_congruence_tactics();
    finalize_congruence_closure();
    finalize_smt_util();
}
}
