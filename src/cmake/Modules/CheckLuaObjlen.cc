/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <memory>
#include <lua.hpp>

// Little program for checking whether lua_objlen is available
int main() {
    lua_State * L;
    L = luaL_newstate();
    lua_newtable(L);
    if (lua_objlen(L, -1) == 0)
        return 0;
    else
        return 1;
}
