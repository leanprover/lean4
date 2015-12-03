/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/forward/init_module.h"
#include "library/blast/forward/forward_extension.h"
#include "library/blast/forward/forward_lemma_set.h"
#include "library/blast/forward/pattern.h"
#include "library/blast/forward/ematch.h"

namespace lean {
namespace blast {

void initialize_forward_module() {
    initialize_forward_extension();
    initialize_pattern();
    initialize_forward_lemma_set();
    initialize_ematch();
}

void finalize_forward_module() {
    finalize_ematch();
    finalize_forward_lemma_set();
    finalize_pattern();
    finalize_forward_extension();
}
}}
