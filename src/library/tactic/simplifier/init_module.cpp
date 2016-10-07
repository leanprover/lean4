/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/trace.h"
#include "library/tactic/simplifier/util.h"
#include "library/tactic/simplifier/simp_lemmas.h"
#include "library/tactic/simplifier/prop_simplifier.h"
#include "library/tactic/simplifier/theory_simplifier.h"
#include "library/tactic/simplifier/simplifier.h"

namespace lean {

void initialize_simplifier_module() {
    register_trace_class("simplifier");

    initialize_simp_util();
    initialize_simp_lemmas();
    initialize_prop_simplifier();
    initialize_theory_simplifier();
    initialize_simplifier();
}

void finalize_simplifier_module() {
    finalize_simplifier();
    finalize_theory_simplifier();
    finalize_prop_simplifier();
    finalize_simp_lemmas();
    finalize_simp_util();
}
}
