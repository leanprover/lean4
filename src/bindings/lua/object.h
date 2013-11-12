/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
class object;
void open_object(lua_State * L);
bool is_object(lua_State * L, int idx);
object & to_object(lua_State * L, int idx);
int push_object(lua_State * L, object const & o);
}
