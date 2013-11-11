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
static void open_state(lua_State * L);

static void copy_values(lua_State * src, int first, int last, lua_State * tgt) {
    for (int i = first; i <= last; i++) {
        if (lua_isstring(src, i)) {
            lua_pushfstring(tgt, lua_tostring(src, i));
        } else if (lua_isnumber(src, i)) {
            lua_pushnumber(tgt, lua_tonumber(src, i));
        } else if (is_expr(src, i)) {
            push_expr(tgt, to_expr(src, i));
        } else if (is_context(src, i)) {
            push_context(tgt, to_context(src, i));
        } else if (is_name(src, i)) {
            push_name(tgt, to_name(src, i));
        } else if (is_mpz(src, i)) {
            push_mpz(tgt, to_mpz(src, i));
        } else if (is_mpq(src, i)) {
            push_mpq(tgt, to_mpq(src, i));
        } else if (is_options(src, i)) {
            push_options(tgt, to_options(src, i));
        } else if (is_sexpr(src, i)) {
            push_sexpr(tgt, to_sexpr(src, i));
        } else if (is_format(src, i)) {
            push_format(tgt, to_format(src, i));
        } else if (is_context_entry(src, i)) {
            push_context_entry(tgt, to_context_entry(src, i));
        } else if (is_local_context(src, i)) {
            push_local_context(tgt, to_local_context(src, i));
        } else if (is_local_entry(src, i)) {
            push_local_entry(tgt, to_local_entry(src, i));
        } else {
            throw exception("unsupported value type for inter-State call");
        }
    }
}

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
        lean::open_state(m_state);
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

    void dostring(char const * str, environment & env) {
        set_environment set(m_state, env);
        dostring(str);
    }

    int dostring(char const * str, lua_State * src, int first, int last) {
        std::lock_guard<std::mutex> lock(m_mutex);

        int sz_before = lua_gettop(m_state);

        int result = luaL_loadstring(m_state, str);
        if (result)
            throw lua_exception(lua_tostring(m_state, -1));

        copy_values(src, first, last, m_state);

        result = lua_pcall(m_state, first > last ? 0 : last - first + 1, LUA_MULTRET, 0);
        if (result)
            throw lua_exception(lua_tostring(m_state, -1));

        int sz_after = lua_gettop(m_state);

        if (sz_after > sz_before) {
            copy_values(m_state, sz_before + 1, sz_after, src);
            lua_pop(m_state, sz_after - sz_before);
        }
        return sz_after - sz_before;
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

void leanlua_state::dostring(char const * str, environment & env) {
    m_ptr->dostring(str, env);
}

int leanlua_state::dostring(char const * str, lua_State * src, int first, int last) {
    return m_ptr->dostring(str, src, first, last);
}

constexpr char const * state_mt = "state.mt";

bool is_state(lua_State * L, int idx) {
    return testudata(L, idx, state_mt);
}

leanlua_state & to_state(lua_State * L, int idx) {
    return *static_cast<leanlua_state*>(luaL_checkudata(L, idx, state_mt));
}

int push_state(lua_State * L, leanlua_state const & s) {
    void * mem = lua_newuserdata(L, sizeof(leanlua_state));
    new (mem) leanlua_state(s);
    luaL_getmetatable(L, state_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mk_state(lua_State * L) {
    leanlua_state r;
    return push_state(L, r);
}

static int state_gc(lua_State * L) {
    to_state(L, 1).~leanlua_state();
    return 0;
}

static int state_dostring(lua_State * L) {
    return to_state(L, 1).dostring(luaL_checkstring(L, 2), L, 3, lua_gettop(L));
}

static const struct luaL_Reg state_m[] = {
    {"__gc",            state_gc},
    {"dostring",        safe_function<state_dostring>},
    {0, 0}
};

static void open_state(lua_State * L) {
    luaL_newmetatable(L, state_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, state_m, 0);

    set_global_function<mk_state>(L, "State");
}
}
