/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/forward/init_module.h"
#include "library/blast/forward/forward_extension.h"
#include "library/blast/forward/pattern.h"

namespace lean {
namespace blast {

void initialize_forward_module() {
    initialize_forward_extension();
    initialize_pattern();
}

void finalize_forward_module() {
    finalize_pattern();
    finalize_forward_extension();
}
}}
