/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "bindings/lua/lua_exception.h"

namespace lean {
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
};
}
