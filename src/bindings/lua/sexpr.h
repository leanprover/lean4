/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
namespace lean {
class sexpr;
void open_sexpr(lua_State * L);
bool is_sexpr(lua_State * L, int idx);
sexpr & to_sexpr(lua_State * L, int idx);
int push_sexpr(lua_State * L, sexpr const & e);
}
