/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/recursor/recursor_action.h"
#include "library/blast/recursor/recursor_strategy.h"

namespace lean {
namespace blast {
void initialize_recursor_module() {
    initialize_recursor_action();
    initialize_recursor_strategy();
}
void finalize_recursor_module() {
    finalize_recursor_strategy();
    finalize_recursor_action();
}
}}
