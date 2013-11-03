/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <cstdlib>

#ifdef LEAN_USE_LUA
#include <lua.hpp>
#include "bindings/lua/name.h"

int main(int argc, char ** argv) {
    int status, result;
    lua_State *L;

    L = luaL_newstate();
    luaL_openlibs(L);
    lean::init_name(L);

    for (int i = 1; i < argc; i++) {
        status = luaL_loadfile(L, argv[i]);
        if (status) {
            std::cerr << "Couldn't load file: " << lua_tostring(L, -1) << "\n";
            return 1;
        }
        result = lua_pcall(L, 0, LUA_MULTRET, 0);
        if (result) {
            std::cerr << "Failed to run script: " << lua_tostring(L, -1) << "\n";
            return 1;
        }
    }
    lua_close(L);
    return 0;
}
#else
int main() {
    std::cerr << "Lean was compiled without Lua support\n";
    return 1;
}
#endif
