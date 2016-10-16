/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/trace.h"
#include "library/tactic/simplifier/simplifier.h"

namespace lean {

void initialize_simplifier_module() {
    register_trace_class("simplifier");

    initialize_simplifier();
}

void finalize_simplifier_module() {
    finalize_simplifier();
}
}
