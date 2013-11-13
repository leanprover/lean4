/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>

namespace lean {
void setfuncs(lua_State * L, luaL_Reg const * l, int nup);
bool testudata(lua_State * L, int idx, char const * mt);
int load(lua_State * L, lua_Reader reader, void * data, char const * source);
size_t objlen(lua_State * L, int idx);
void dofile(lua_State * L, char const * fname);
void dostring(lua_State * L, char const * str);
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

#define SET_GLOBAL_FUN(F, N) set_global_function<F>(L, N)

// Auxiliary macro for creating a Lua table that stores enumeration values
#define SET_ENUM(N, V) lua_pushstring(L, N); lua_pushinteger(L, static_cast<int>(V)); lua_settable(L, -3)
}
