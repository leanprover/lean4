/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>

namespace lean {
/**
   \brief Reference to Lua object.
*/
class lua_ref {
    lua_State * m_state;
    int         m_ref;
public:
    lua_ref():m_state(nullptr) {}
    /**
       \brief Create a reference to the Lua object at position \c i on \c L stack.
    */
    lua_ref(lua_State * L, int i);
    lua_ref(lua_ref const & r);
    lua_ref(lua_ref && r);
    ~lua_ref();
    lua_ref & operator=(lua_ref const & r);
    void push() const;
    lua_State * get_state() const { return m_state; }
};

/**
   \brief '<' functor for lua_ref.
*/
struct lua_ref_lt_proc {
    int operator()(lua_ref const & r1, lua_ref const & r2) const;
};
}
