/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "util/sexpr/sexpr.h"
#include "util/sexpr/options.h"
#include "util/sexpr/format.h"

namespace lean {
inline void open_sexpr_module(lua_State * L) {
    open_sexpr(L);
    open_options(L);
    open_format(L);
}
inline void register_sexpr_module() {
    script_state::register_module(open_sexpr_module);
}
}
