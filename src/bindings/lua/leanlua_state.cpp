/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <mutex>
#include <string>
#include <lua.hpp>
#include "util/debug.h"
#include "util/exception.h"
#include "util/memory.h"
#include "bindings/lua/leanlua_state.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/numerics.h"
#include "bindings/lua/options.h"
#include "bindings/lua/sexpr.h"
#include "bindings/lua/format.h"
#include "bindings/lua/level.h"
#include "bindings/lua/local_context.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/environment.h"
#include "bindings/lua/lean.lua"

extern "C" void * lua_realloc(void *, void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }

namespace lean {
struct leanlua_state::imp {
    lua_State * m_state;
    std::mutex  m_mutex;

    imp() {
        #ifdef LEAN_USE_LUA_NEWSTATE
        m_state = lua_newstate(lua_realloc, nullptr);
        #else
        m_state = luaL_newstate();
        #endif
        if (m_state == nullptr)
            throw exception("fail to create Lua interpreter");
        luaL_openlibs(m_state);
        lean::open_name(m_state);
        lean::open_mpz(m_state);
        lean::open_mpq(m_state);
        lean::open_options(m_state);
        lean::open_sexpr(m_state);
        lean::open_format(m_state);
        lean::open_level(m_state);
        lean::open_local_context(m_state);
        lean::open_expr(m_state);
        lean::open_context(m_state);
        lean::open_environment(m_state);
        dostring(g_leanlua_extra);
    }

    ~imp() {
        lua_close(m_state);
    }

    void dofile(char const * fname) {
        std::lock_guard<std::mutex> lock(m_mutex);
        ::lean::dofile(m_state, fname);
    }

    void dostring(char const * str) {
        std::lock_guard<std::mutex> lock(m_mutex);
        ::lean::dostring(m_state, str);
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
