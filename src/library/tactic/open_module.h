/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/cex_builder.h"
#include "library/tactic/proof_state.h"

namespace lean {
inline void open_tactic_module(lua_State * L) {
    open_goal(L);
    open_proof_builder(L);
    open_cex_builder(L);
    open_proof_state(L);
}
}
