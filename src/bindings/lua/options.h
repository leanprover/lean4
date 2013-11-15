/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
namespace lean {
UDATA_DEFS(options)
void open_options(lua_State * L);
/**
   \brief Return the set of options associated with the given Lua State.
   This procedure checks for options at:
   1- Lean state object associated with \c L
   2- Lua Registry associated with \c L
*/
options get_global_options(lua_State * L);
/**
   \brief Update the set of options associated with the given Lua State.
   If \c L is associated with a Lean state object \c S, then we update the options of \c S.
   Otherwise, we update the registry of \c L.
*/
void set_global_options(lua_State * L, options const & o);
}
