/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
namespace lean {
class expr;
void open_expr(lua_State * L);
bool is_expr(lua_State * L, int idx);
expr & to_expr(lua_State * L, int idx);
int push_expr(lua_State * L, expr const & o);
}
#endif
