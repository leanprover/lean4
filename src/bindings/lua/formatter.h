/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
class formatter;
void open_formatter(lua_State * L);
bool is_formatter(lua_State * L, int idx);
formatter & to_formatter(lua_State * L, int idx);
int push_formatter(lua_State * L, formatter const & o);
}
