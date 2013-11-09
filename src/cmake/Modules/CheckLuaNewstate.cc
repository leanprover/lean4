/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <memory>
#include <cstdlib>
#include <lua.hpp>

static void * lua_realloc(void *, void * q, size_t, size_t sz) { return realloc(q, sz); }

// Little program for checking whether lua_newstate is available
int main() {
    lua_State * L;
    L = lua_newstate(lua_realloc, 0);
    lua_close(L);
    return 0;
}
