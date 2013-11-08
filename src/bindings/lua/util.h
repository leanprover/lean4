/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
namespace lean {
void setfuncs(lua_State * L, luaL_Reg const * l, int nup);
bool testudata(lua_State * L, int idx, char const * mt);
/**
   \brief Wrapper for invoking function f, and catching Lean exceptions.
*/
int safe_function_wrapper(lua_State * L, lua_CFunction f);
template<lua_CFunction F> int safe_function(lua_State * L) {
    return safe_function_wrapper(L, F);
}
template<lua_CFunction F> void set_global_function(lua_State * L, char const * name) {
    lua_pushcfunction(L, safe_function<F>);
    lua_setglobal(L, name);
}
}
#endif
