/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
#include "library/state.h"

namespace lean {
/**
   \brief Auxiliary class for temporarily setting the Lua registry of a Lua state
   with a Lean state object.
*/
class set_state {
    lua_State * m_state;
public:
    set_state(lua_State * L, state & st);
    ~set_state();
};
/**
   \brief Return the Lean state object associated with the given Lua state.
   Return nullptr is there is none.
*/
state * get_state(lua_State * L);
}
