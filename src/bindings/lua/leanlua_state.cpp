/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "bindings/lua/leanlua_state.h"

#ifdef LEAN_USE_LUA
#include <lua.hpp>
#include <mutex>
#include "util/exception.h"
#include "bindings/lua/name.h"
#include "bindings/lua/numerics.h"
#include "bindings/lua/options.h"
#include "bindings/lua/sexpr.h"

namespace lean {
struct leanlua_state::imp {
    lua_State * m_state;
    std::mutex  m_mutex;
    imp() {
        m_state = luaL_newstate();
        luaL_openlibs(m_state);
        lean::open_name(m_state);
        lean::open_mpz(m_state);
        lean::open_mpq(m_state);
        lean::open_options(m_state);
        lean::open_sexpr(m_state);
    }
    ~imp() {
        lua_close(m_state);
    }

    void exec() {
        int result = lua_pcall(m_state, 0, LUA_MULTRET, 0);
        if (result)
            throw exception(lua_tostring(m_state, -1));
    }

    void dofile(char const * fname) {
        std::lock_guard<std::mutex> lock(m_mutex);
        int result = luaL_loadfile(m_state, fname);
        if (result)
            throw exception(lua_tostring(m_state, -1));
        exec();
    }

    void dostring(char const * str) {
        std::lock_guard<std::mutex> lock(m_mutex);
        int result = luaL_loadstring(m_state, str);
        if (result)
            throw exception(lua_tostring(m_state, -1));
        exec();
    }
};

leanlua_state::leanlua_state():
    m_ptr(new imp()) {
}

leanlua_state::~leanlua_state() {
}

void leanlua_state::dofile(char const * fname) {
    m_ptr->dofile(fname);
}

void leanlua_state::dostring(char const * str) {
    m_ptr->dostring(str);
}
}
#else
leanlua_state::leanlua_state() {
}

leanlua_state::~leanlua_state() {
}

[[ noreturn ]] void throw_lua_not_supported() {
    throw exception("Lean was compiled without Lua support");
}

void leanlua_state::dofile(char const * fname) {
    throw_lua_not_supported();
}

void leanlua_state::dostring(char const * str) {
    throw_lua_not_supported();
}
#endif
