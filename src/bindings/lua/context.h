/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
class context_entry;
bool is_context_entry(lua_State * L, int idx);
context_entry & to_context_entry(lua_State * L, int idx);
int push_context_entry(lua_State * L, context_entry const & o);

class context;
bool is_context(lua_State * L, int idx);
context & to_context(lua_State * L, int idx);
int push_context(lua_State * L, context const & o);

void open_context(lua_State * L);
}
