/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lua.h"
#pragma once

namespace lean {
/**
   \brief Reference to Lua object.
*/
class luaref {
    lua_State * m_state;
    int         m_ref;
public:
    luaref():m_state(nullptr), m_ref(0) {}
    /**
       \brief Create a reference to the Lua object at position \c i on \c L stack.
    */
    luaref(lua_State * L, int i);
    luaref(luaref const & r);
    luaref(luaref && r);
    ~luaref();
    void release();
    luaref & operator=(luaref const & r);
    void push() const;
    lua_State * get_state() const { return m_state; }
};

/**
   \brief '<' functor for luaref.
*/
struct luaref_lt_proc {
    int operator()(luaref const & r1, luaref const & r2) const;
};
}
