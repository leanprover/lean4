/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
namespace lean {
class name;
void open_name(lua_State * L);
bool is_name(lua_State * L, int idx);
name & to_name(lua_State * L, int idx);
name to_name_ext(lua_State * L, int idx);
int push_name(lua_State * L, name const & n);
}
#endif
