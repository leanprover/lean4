/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
namespace lean {
class options;
void open_options(lua_State * L);
bool is_options(lua_State * L, int idx);
options & to_options(lua_State * L, int idx);
int push_options(lua_State * L, options const & o);
}
#endif
