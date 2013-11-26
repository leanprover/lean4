/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>
#include "library/io_state.h"

namespace lean {
UDATA_DEFS(io_state)
void open_io_state(lua_State * L);
/**
   \brief Auxiliary class for temporarily setting the Lua registry of a Lua state
   with a Lean io_state object.
*/
class set_io_state {
    lua_State * m_state;
    io_state *  m_prev;
public:
    set_io_state(lua_State * L, io_state & st);
    ~set_io_state();
};
/**
   \brief Return the Lean state object associated with the given Lua state.
   Return nullptr is there is none.
*/
io_state * get_io_state(lua_State * L);
}
