/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
#include "kernel/expr.h"
namespace lean {
bool is_local_entry(lua_State * L, int idx);
local_entry & to_local_entry(lua_State * L, int idx);
int push_local_entry(lua_State * L, local_entry const & o);

bool is_local_context(lua_State * L, int idx);
local_context & to_local_context(lua_State * L, int idx);
int push_local_context(lua_State * L, local_context const & o);

void open_local_context(lua_State * L);
}
