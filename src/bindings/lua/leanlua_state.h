/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <lua.hpp>
#include "bindings/lua/lua_exception.h"

namespace lean {
class environment;
/**
   \brief Wrapper for lua_State objects which contains all Lean bindings.
*/
class leanlua_state {
    struct imp;
    std::shared_ptr<imp> m_ptr;
public:
    leanlua_state();
    ~leanlua_state();

    /**
       \brief Execute the file with the given name.
       This method throws an exception if an error occurs.
    */
    void dofile(char const * fname);
    /**
       \brief Execute the given string.
       This method throws an exception if an error occurs.
    */
    void dostring(char const * str);

    /**
       \brief Execute the given script, but sets the registry with the given environment object.
       The registry can be accessed by \str by invoking the function <tt>env()</tt>.
       The script \c str should not store a reference to the environment \c env.
    */
    void dostring(char const * str, environment & env);

    /**
       \brief Execute the given script, but copy the values at positions <tt>[first, last]</tt> from the stack of \c src.
       The values are passed as arguments to the script \c str.
       The values returned by the script \c str are copied back to the stack of \c src.
       The result is the number of values returned by the script \c str.
    */
    int dostring(char const * str, lua_State * src, int first, int last);
};
}
