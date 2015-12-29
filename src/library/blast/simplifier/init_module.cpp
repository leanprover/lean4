/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/simplifier/simplifier_actions.h"
#include "library/blast/simplifier/simp_lemmas.h"
#include "library/blast/simplifier/simplifier.h"

namespace lean {
namespace blast {

void initialize_simplifier_module() {
    initialize_simp_lemmas();
    initialize_simplifier();
    initialize_simplifier_actions();
}

void finalize_simplifier_module() {
    finalize_simplifier_actions();
    finalize_simplifier();
    finalize_simp_lemmas();
}
}}
