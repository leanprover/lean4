/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
#include "util/debug.h"
#include "util/name.h"
#include "util/sstream.h"
#include "bindings/lua/util.h"

namespace lean {
DECL_UDATA(name)

static int mk_name(lua_State * L) {
    int nargs = lua_gettop(L);
    name r;
    for (int i = 1; i <= nargs; i++) {
        switch (lua_type(L, i)) {
        case LUA_TNIL:      break; // skip
        case LUA_TNUMBER:   r = name(r, lua_tointeger(L, i)); break;
        case LUA_TSTRING:   r = name(r, lua_tostring(L, i)); break;
        case LUA_TUSERDATA: r = r + to_name(L, i); break;
        default:            throw exception(sstream() << "arg #" << i << " must be a hierarchical name, string, or integer");
        }
    }
    return push_name(L, r);
}

name to_name_ext(lua_State * L, int idx) {
    if (lua_isstring(L, idx)) {
        return luaL_checkstring(L, idx);
    } else if (lua_istable(L, idx)) {
        name r;
        int n = objlen(L, idx);
        for (int i = 1; i <= n; i++) {
            lua_rawgeti(L, idx, i);
            switch (lua_type(L, -1)) {
            case LUA_TNIL:      break; // skip
            case LUA_TNUMBER:   r = name(r, lua_tointeger(L, -1)); break;
            case LUA_TSTRING:   r = name(r, lua_tostring(L, -1));  break;
            case LUA_TUSERDATA: r = r + to_name(L, -1); break;
            default:            throw exception("invalid array arguments, elements must be a hierarchical name, string, or integer");
            }
            lua_pop(L, 1);
        }
        return r;
    } else {
        return to_name(L, idx);
    }
}

static int name_tostring(lua_State * L) {
    lua_pushstring(L, to_name(L, 1).to_string().c_str());
    return 1;
}

static int name_eq(lua_State * L) {
    lua_pushboolean(L, to_name(L, 1) == to_name(L, 2));
    return 1;
}

static int name_lt(lua_State * L) {
    lua_pushboolean(L, to_name(L, 1) < to_name(L, 2));
    return 1;
}

static int name_hash(lua_State * L) {
    lua_pushinteger(L, to_name(L, 1).hash());
    return 1;
}

static const struct luaL_Reg name_m[] = {
    {"__gc",       name_gc}, // never throws
    {"__tostring", safe_function<name_tostring>},
    {"__eq",       safe_function<name_eq>},
    {"__lt",       safe_function<name_lt>},
    {"hash",       safe_function<name_hash>},
    {0, 0}
};

void open_name(lua_State * L) {
    luaL_newmetatable(L, name_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, name_m, 0);

    SET_GLOBAL_FUN(mk_name,   "name");
    SET_GLOBAL_FUN(name_pred, "is_name");
}
}
