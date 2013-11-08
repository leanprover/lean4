/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
class level;
void open_level(lua_State * L);
bool is_level(lua_State * L, int idx);
level & to_level(lua_State * L, int idx);
int push_level(lua_State * L, level const & o);
}
