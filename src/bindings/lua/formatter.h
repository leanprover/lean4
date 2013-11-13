/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
class formatter;
void open_formatter(lua_State * L);
bool is_formatter(lua_State * L, int idx);
formatter & to_formatter(lua_State * L, int idx);
int push_formatter(lua_State * L, formatter const & o);
/**
   \brief Return the formatter object associated with the given Lua State.
   This procedure checks for options at:
   1- Lean state object associated with \c L
   2- Lua Registry associated with \c L
*/
formatter get_global_formatter(lua_State * L);
/**
   \brief Update the formatter object associated with the given Lua State.
   If \c L is associated with a Lean state object \c S, then we update the formatter of \c S.
   Otherwise, we update the registry of \c L.
*/
void set_global_formatter(lua_State * L, formatter const & fmt);
}
