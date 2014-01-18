/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "library/simplifier/ceq.h"
#include "library/simplifier/rewrite_rule_set.h"
#include "library/simplifier/simplifier.h"

namespace lean {
inline void open_simplifier_module(lua_State * L) {
    open_ceq(L);
    open_rewrite_rule_set(L);
    open_simplifier(L);
}
inline void register_simplifier_module() {
    script_state::register_module(open_simplifier_module);
}
}
