/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_set.h"

namespace lean {
name mk_unique(name_set const & s, name const & suggestion) {
    name n = suggestion;
    int i  = 1;
    while (true) {
        if (!s.contains(n))
            return n;
        n = name(suggestion, i);
        i++;
    }
}

name_set to_name_set(buffer<name> const & ns) {
    name_set r;
    for (name const & n : ns)
        r.insert(n);
    return r;
}

DECL_UDATA(name_set)
static int mk_name_set(lua_State * L) {
    name_set r;
    int nargs = lua_gettop(L);
    for (int i = 1; i <= nargs; i++)
        r.insert(to_name_ext(L, i));
    return push_name_set(L, r);
}
static int name_set_insert(lua_State * L) { return push_name_set(L, insert(to_name_set(L, 1), to_name_ext(L, 2))); }
static int name_set_contains(lua_State * L) { return push_boolean(L, to_name_set(L, 1).contains(to_name_ext(L, 2))); }
static int name_set_erase(lua_State * L) { return push_name_set(L, erase(to_name_set(L, 1), to_name_ext(L, 2))); }

static const struct luaL_Reg name_set_m[] = {
    {"__gc",     name_set_gc}, // never throws
    {"insert",   safe_function<name_set_insert>},
    {"contains", safe_function<name_set_contains>},
    {"erase",    safe_function<name_set_erase>},
    {0, 0}
};

void open_name_set(lua_State * L) {
    luaL_newmetatable(L, name_set_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, name_set_m, 0);

    SET_GLOBAL_FUN(mk_name_set,   "name_set");
    SET_GLOBAL_FUN(name_set_pred, "is_name_set");
}
}
