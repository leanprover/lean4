/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/blast/unit/unit_action.h"

namespace lean {
namespace blast {

void initialize_unit_module() {
    initialize_unit_action();
}

void finalize_unit_module() {
    finalize_unit_action();
}
}}
