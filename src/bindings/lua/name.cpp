/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
#include "util/debug.h"
#include "util/name.h"
#include "bindings/lua/util.h"

namespace lean {
static int name_gc(lua_State * L);
static int name_tostring(lua_State * L);
static int name_eq(lua_State * L);
static int name_lt(lua_State * L);

static const struct luaL_Reg name_m[] = {
    {"__gc",       name_gc}, // never throws
    {"__tostring", safe_function<name_tostring>},
    {"__eq",       safe_function<name_eq>},
    {"__lt",       safe_function<name_lt>},
    {0, 0}
};

static int mk_name(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs != 1 && nargs != 2)
        return luaL_error(L, "function 'name' expects 1 or 2 arguments");
    if (nargs == 1) {
        char const * str = luaL_checkstring(L, 1);
        void * mem = lua_newuserdata(L, sizeof(name));
        new (mem) name(str);
    } else {
        lean_assert(nargs == 2);
        name tmp;
        name * prefix;
        if (lua_isstring(L, 1)) {
            char const * str = luaL_checkstring(L, 1);
            tmp    = name(str);
            prefix = &tmp;
        } else {
            prefix = static_cast<name*>(luaL_checkudata(L, 1, "name.mt"));
        }
        if (lua_isstring(L, 2)) {
            char const * str = luaL_checkstring(L, 2);
            void * mem = lua_newuserdata(L, sizeof(name));
            new (mem) name(*prefix, str);
        } else {
            int idx = luaL_checkinteger(L, 2);
            void * mem = lua_newuserdata(L, sizeof(name));
            new (mem) name(*prefix, idx);
        }
    }
    luaL_getmetatable(L, "name.mt");
    lua_setmetatable(L, -2);
    return 1;
}

static int name_gc(lua_State * L) {
    name * n = static_cast<name*>(luaL_checkudata(L, 1, "name.mt"));
    n->~name();
    return 0;
}

static int name_tostring(lua_State * L) {
    name * n = static_cast<name*>(luaL_checkudata(L, 1, "name.mt"));
    lua_pushfstring(L, n->to_string().c_str());
    return 1;
}

static int name_eq(lua_State * L) {
    name * n1 = static_cast<name*>(luaL_checkudata(L, 1, "name.mt"));
    name * n2 = static_cast<name*>(luaL_checkudata(L, 2, "name.mt"));
    lua_pushboolean(L, *n1 == *n2);
    return 1;
}

static int name_lt(lua_State * L) {
    name * n1 = static_cast<name*>(luaL_checkudata(L, 1, "name.mt"));
    name * n2 = static_cast<name*>(luaL_checkudata(L, 2, "name.mt"));
    lua_pushboolean(L, *n1 < *n2);
    return 1;
}

void init_name(lua_State * L) {
    luaL_newmetatable(L, "name.mt");
    setfuncs(L, name_m, 0);

    lua_pushcfunction(L, safe_function<mk_name>);
    lua_setglobal(L, "name");
}
}
#endif
