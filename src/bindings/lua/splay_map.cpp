/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
#include "util/splay_map.h"
#include "bindings/lua/util.h"
#include "bindings/lua/lref.h"

namespace lean {
typedef splay_map<lref, lref, lref_lt_proc> lua_splay_map;

constexpr char const * splay_map_mt = "splay_map.mt";

bool is_splay_map(lua_State * L, int idx) {
    return testudata(L, idx, splay_map_mt);
}

lua_splay_map & to_splay_map(lua_State * L, int idx) {
    return *static_cast<lua_splay_map*>(luaL_checkudata(L, idx, splay_map_mt));
}

int push_splay_map(lua_State * L, lua_splay_map const & o) {
    void * mem = lua_newuserdata(L, sizeof(lua_splay_map));
    new (mem) lua_splay_map(o);
    luaL_getmetatable(L, splay_map_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mk_splay_map(lua_State * L) {
    lua_splay_map r;
    return push_splay_map(L, r);
}

static int splay_map_gc(lua_State * L) {
    to_splay_map(L, 1).~lua_splay_map();
    return 0;
}

static int splay_map_size(lua_State * L) {
    lua_pushinteger(L, to_splay_map(L, 1).size());
    return 1;
}

static int splay_map_contains(lua_State * L) {
    lua_pushboolean(L, to_splay_map(L, 1).contains(lref(L, 2)));
    return 1;
}

static int splay_map_empty(lua_State * L) {
    lua_pushboolean(L, to_splay_map(L, 1).empty());
    return 1;
}

static int splay_map_insert(lua_State * L) {
    to_splay_map(L, 1).insert(lref(L, 2), lref(L, 3));
    return 0;
}

static int splay_map_erase(lua_State * L) {
    to_splay_map(L, 1).erase(lref(L, 2));
    return 0;
}

static int splay_map_find(lua_State * L) {
    lua_splay_map & m = to_splay_map(L, 1);
    lref * val = m.splay_find(lref(L, 2));
    if (val) {
        lean_assert(val->get_state() == L);
        val->push();
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int splay_map_copy(lua_State * L) {
    return push_splay_map(L, to_splay_map(L, 1));
}

static int splay_map_pred(lua_State * L) {
    lua_pushboolean(L, is_splay_map(L, 1));
    return 1;
}

static int splay_map_for_each(lua_State * L) {
    // Remark: we take a copy of the map to make sure
    // for_each will not crash if the map is updated while being
    // traversed.
    // The copy operation is very cheap O(1).
    lua_splay_map m(to_splay_map(L, 1)); // map
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    m.for_each([&](lref const & k, lref const & v) {
        lua_pushvalue(L, 2); // push user-fun
        k.push();
        v.push();
        pcall(L, 2, 0, 0);
        });
    return 0;
}

static const struct luaL_Reg splay_map_m[] = {
    {"__gc",            splay_map_gc}, // never throws
    {"__len",           safe_function<splay_map_size> },
    {"contains",        safe_function<splay_map_contains>},
    {"size",            safe_function<splay_map_size>},
    {"empty",           safe_function<splay_map_empty>},
    {"insert",          safe_function<splay_map_insert>},
    {"erase",           safe_function<splay_map_erase>},
    {"find",            safe_function<splay_map_find>},
    {"copy",            safe_function<splay_map_copy>},
    {"for_each",        safe_function<splay_map_for_each>},
    {0, 0}
};

void open_splay_map(lua_State * L) {
    luaL_newmetatable(L, splay_map_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, splay_map_m, 0);

    SET_GLOBAL_FUN(mk_splay_map,          "splay_map");
    SET_GLOBAL_FUN(splay_map_pred,        "is_splay_map");
}
}
