/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <mutex>
#include <lua.hpp>
#include "util/unlock_guard.h"

namespace lean {
/**
   \brief Wrapper for lua_State objects which contains all Lean bindings.
*/
class script_state {
public:
    struct imp;
private:
    std::shared_ptr<imp> m_ptr;
    script_state(std::weak_ptr<imp> const & ptr);
    friend script_state to_script_state(lua_State * L);
    std::mutex & get_mutex();
    lua_State * get_state();
    friend class data_channel;
public:
    script_state();
    ~script_state();

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
       \brief Execute \c f in the using the internal Lua State.
    */
    template<typename F>
    typename std::result_of<F(lua_State * L)>::type apply(F && f) {
        std::lock_guard<std::mutex> lock(get_mutex());
        return f(get_state());
    }

    typedef void (*reg_fn)(lua_State *); // NOLINT
    static void register_module(reg_fn f);

    static void register_code(char const * code);

    /**
       \brief Auxiliary function for writing API bindings
       that release the lock to this object while executing
       \c f.
    */
    template<typename F>
    void exec_unprotected(F && f) {
        unlock_guard unlock(get_mutex());
        f();
    }

    template<typename F>
    void exec_protected(F && f) {
        std::lock_guard<std::mutex> lock(get_mutex());
        f();
    }
};
/**
   \brief Return a reference to the script_state object that is wrapping \c L.
*/
script_state to_script_state(lua_State * L);
}
