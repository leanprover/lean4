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
class lref {
    lua_State * m_state;
    int         m_ref;
public:
    lref():m_state(nullptr) {}
    /**
       \brief Create a reference to the Lua object at position \c i on \c L stack.
    */
    lref(lua_State * L, int i);
    lref(lref const & r);
    lref(lref && r);
    ~lref();
    lref & operator=(lref const & r);
    void push() const;
    lua_State * get_state() const { return m_state; }
};

/**
   \brief '<' functor for lref.
*/
struct lref_lt_proc {
    int operator()(lref const & r1, lref const & r2) const;
};
}
