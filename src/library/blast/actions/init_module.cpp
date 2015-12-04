/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/actions/recursor_action.h"

namespace lean {
namespace blast {
void initialize_actions_module() {
    initialize_recursor_action();
}
void finalize_actions_module() {
    finalize_recursor_action();
}
}}
