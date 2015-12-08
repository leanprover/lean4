/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/grinder/init_module.h"
#include "library/blast/grinder/intro_elim_lemmas.h"
#include "library/blast/grinder/grinder_actions.h"

namespace lean {
namespace blast {
void initialize_grinder_module() {
    initialize_intro_elim_lemmas();
    initialize_grinder_actions();
}

void finalize_grinder_module() {
    finalize_grinder_actions();
    finalize_intro_elim_lemmas();
}
}}
