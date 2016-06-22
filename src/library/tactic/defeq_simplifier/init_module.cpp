/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/tactic/defeq_simplifier/defeq_simplifier.h"
#include "library/tactic/defeq_simplifier/defeq_simp_lemmas.h"

namespace lean {

void initialize_defeq_simplifier_module() {
    initialize_defeq_simp_lemmas();
    initialize_defeq_simplifier();
}

void finalize_defeq_simplifier_module() {
    finalize_defeq_simplifier();
    finalize_defeq_simp_lemmas();
}
}
