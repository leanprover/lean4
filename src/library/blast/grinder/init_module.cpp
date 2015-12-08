/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/grinder/init_module.h"
#include "library/blast/grinder/intro_elim_lemmas.h"

namespace lean {
namespace blast {
void initialize_grinder_module() {
    initialize_intro_elim_lemmas();
}

void finalize_grinder_module() {
    finalize_intro_elim_lemmas();
}
}}
