/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <lua.hpp>
#include "library/script_evaluator.h"
#include "bindings/lua/lua_exception.h"

namespace lean {
class environment;
class state;
/**
   \brief Wrapper for lua_State objects which contains all Lean bindings.
*/
class leanlua_state : public script_evaluator {
public:
    struct imp;
private:
    std::shared_ptr<imp> m_ptr;
    leanlua_state(std::weak_ptr<imp> const & ptr);
    friend class leanlua_thread;
    friend class data_channel;
    friend int state_dostring(lua_State * L);
    friend int state_set_global(lua_State * L);
    friend int mk_thread(lua_State * L);
    friend int thread_wait(lua_State * L);
    friend leanlua_state to_leanlua_state(lua_State * L);
public:
    leanlua_state();
    virtual ~leanlua_state();

    /**
       \brief Execute the file with the given name.
       This method throws an exception if an error occurs.
    */
    void dofile(char const * fname);
    /**
       \brief Execute the given string.
       This method throws an exception if an error occurs.
    */
    virtual void dostring(char const * str);

    /**
       \brief Execute the given script, but sets the registry with the given environment object.
       The registry can be accessed by \str by invoking the function <tt>env()</tt>.
       The script \c str should not store a reference to the environment \c env.
    */
    virtual void dostring(char const * str, environment & env, state & st);
};
/**
   \brief Return a reference to the leanlua_state object that is wrapping \c L.
*/
leanlua_state to_leanlua_state(lua_State * L);
}
