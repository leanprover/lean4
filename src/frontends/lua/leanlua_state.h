/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <mutex>
#include <lua.hpp>
#include "util/lua_exception.h"
#include "library/script_evaluator.h"

namespace lean {
class environment;
class io_state;
/**
   \brief Wrapper for lua_State objects which contains all Lean bindings.
*/
class leanlua_state : public script_evaluator {
public:
    struct imp;
private:
    std::shared_ptr<imp> m_ptr;
    leanlua_state(std::weak_ptr<imp> const & ptr);
    friend leanlua_state to_leanlua_state(lua_State * L);
    std::recursive_mutex & get_mutex();
    lua_State * get_state();
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
    virtual void dostring(char const * str, environment & env, io_state & st);

    /**
       \brief Execute \c f in the using the internal Lua State.
    */
    template<typename F>
    typename std::result_of<F(lua_State * L)>::type apply(F && f) {
        std::lock_guard<std::recursive_mutex> lock(get_mutex());
        return f(get_state());
    }

    /**
       \brief Similar to \c apply, but a lock is not used to guarantee
       exclusive access to the lua_State object.

       \warning It is the caller resposability to guarantee that the object is not being
       concurrently accessed.
    */
    template<typename F>
    typename std::result_of<F(lua_State * L)>::type unguarded_apply(F && f) {
        return f(get_state());
    }
};
/**
   \brief Return a reference to the leanlua_state object that is wrapping \c L.
*/
leanlua_state to_leanlua_state(lua_State * L);
}
