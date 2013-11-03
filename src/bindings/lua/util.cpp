/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <lua.hpp>
namespace lean {
/**
   \brief luaL_setfuncs replacement. The function luaL_setfuncs is only available in Lua 5.2.
*/
void setfuncs(lua_State * L, luaL_Reg const * l, int nup) {
    luaL_checkstack(L, nup, "too many upvalues");
    for (; l->name != NULL; l++) {
        // fill the table with given functions
        for (int i = 0; i < nup; i++) // copy upvalues to the top
            lua_pushvalue(L, -nup);
        lua_pushcclosure(L, l->func, nup);  // closure with those upvalues
        lua_setfield(L, -(nup + 2), l->name);
    }
    lua_pop(L, nup);  // remove upvalues
}
}
#endif
