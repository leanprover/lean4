/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/expr.h"

namespace lean {
bool hop_match(expr const & p, expr const & t, buffer<optional<expr>> & subst);
void open_hop_match(lua_State * L);
}
