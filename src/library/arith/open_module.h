/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/arith/nat.h"
#include "library/arith/int.h"
#include "library/arith/real.h"

namespace lean {
inline void open_arith_module(lua_State * L) {
    open_nat(L);
    open_int(L);
    open_real(L);
}
}
