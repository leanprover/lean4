/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
namespace lean {
class format;
void open_format(lua_State * L);
bool is_format(lua_State * L, int idx);
format & to_format(lua_State * L, int idx);
int push_format(lua_State * L, format const & o);
}
