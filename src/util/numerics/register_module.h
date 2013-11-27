/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"

namespace lean {
inline void open_numerics_module(lua_State * L) {
    open_mpz(L);
    open_mpq(L);
}
inline void register_numerics_module() {
    script_state::register_module(open_numerics_module);
}
}
