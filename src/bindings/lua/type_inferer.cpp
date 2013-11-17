/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "library/type_inferer.h"
#include "bindings/lua/util.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/environment.h"

namespace lean {
constexpr char const * type_inferer_mt = "type_inferer";
type_inferer & to_type_inferer(lua_State * L, int i) { return *static_cast<type_inferer*>(luaL_checkudata(L, i, type_inferer_mt)); }
DECL_PRED(type_inferer)
DECL_GC(type_inferer)

static int type_inferer_call(lua_State * L) {
    int nargs = lua_gettop(L);
    type_inferer & inferer = to_type_inferer(L, 1);
    if (nargs == 2)
        return push_expr(L, inferer(to_nonnull_expr(L, 2)));
    else
        return push_expr(L, inferer(to_nonnull_expr(L, 2), to_context(L, 3)));
}

static int type_inferer_clear(lua_State * L) {
    to_type_inferer(L, 1).clear();
    return 0;
}

static int mk_type_inferer(lua_State * L) {
    void * mem = lua_newuserdata(L, sizeof(type_inferer));
    new (mem) type_inferer(to_environment(L, 1));
    luaL_getmetatable(L, type_inferer_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static const struct luaL_Reg type_inferer_m[] = {
    {"__gc",            type_inferer_gc}, // never throws
    {"__call",          safe_function<type_inferer_call>},
    {"clear",           safe_function<type_inferer_clear>},
    {0, 0}
};

void open_type_inferer(lua_State * L) {
    luaL_newmetatable(L, type_inferer_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, type_inferer_m, 0);

    SET_GLOBAL_FUN(mk_type_inferer,          "type_inferer");
    SET_GLOBAL_FUN(type_inferer_pred,        "is_type_inferer");
}
}
