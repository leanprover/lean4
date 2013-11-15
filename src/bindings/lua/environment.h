/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
#include "kernel/threadsafe_environment.h"

namespace lean {
UDATA_DEFS(environment)
void open_environment(lua_State * L);
/**
   \brief Auxiliary class for setting the Lua registry of a Lua state
   with an environment object.
*/
class set_environment {
    lua_State * m_state;
public:
    set_environment(lua_State * L, environment & env);
    ~set_environment();
};

/**
   \brief Helper class for getting a read-only reference
   for an environment object on the Lua stack.
*/
class ro_environment : public read_only_environment {
public:
    ro_environment(lua_State * L, int idx);
    ro_environment(lua_State * L);
};

/**
   \brief Helper class for getting a read-write reference
   for an environment object on the Lua stack.
*/
class rw_environment : public read_write_environment {
public:
    rw_environment(lua_State * L, int idx);
    rw_environment(lua_State * L);
};
}
