/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
// #include "library/tactic/simplify_tactic.h"

namespace lean {
inline void open_tactic_module(lua_State * L) {
    open_goal(L);
    open_proof_state(L);
    open_tactic(L);
    // open_simplify_tactic(L);
}
inline void register_tactic_module() {
    script_state::register_module(open_tactic_module);
}
}
