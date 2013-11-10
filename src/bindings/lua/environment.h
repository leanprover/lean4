/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
class environment;
void open_environment(lua_State * L);
bool is_environment(lua_State * L, int idx);
environment & to_environment(lua_State * L, int idx);
int push_environment(lua_State * L, environment const & o);
}
