/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/backward/init_module.h"
#include "library/blast/backward/backward_lemmas.h"
#include "library/blast/backward/backward_strategy.h"

namespace lean {
namespace blast {

void initialize_backward_module() {
    initialize_backward_lemmas();
    initialize_backward_strategy();
}

void finalize_backward_module() {
    finalize_backward_strategy();
    finalize_backward_lemmas();
}
}
}
