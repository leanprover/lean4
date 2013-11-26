/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
UDATA_DEFS(cex_builder)
void open_cex_builder(lua_State * L);
}
