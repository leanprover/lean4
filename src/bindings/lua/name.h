/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
UDATA_DEFS(name)
void open_name(lua_State * L);
name to_name_ext(lua_State * L, int idx);
}
