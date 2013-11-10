/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "kernel/environment.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/level.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/environment.h"

namespace lean {
constexpr char const * environment_mt = "environment.mt";

bool is_environment(lua_State * L, int idx) {
    return testudata(L, idx, environment_mt);
}

environment & to_environment(lua_State * L, int idx) {
    return *static_cast<environment*>(luaL_checkudata(L, idx, environment_mt));
}

static int environment_gc(lua_State * L) {
    to_environment(L, 1).~environment();
    return 0;
}

int push_environment(lua_State * L, environment const & env) {
    void * mem = lua_newuserdata(L, sizeof(environment));
    new (mem) environment(env);
    luaL_getmetatable(L, environment_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mk_environment(lua_State * L) {
    return push_environment(L, environment());
}

static int environment_add_uvar(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        to_environment(L, 1).add_uvar(to_name_ext(L, 2));
    else
        to_environment(L, 1).add_uvar(to_name_ext(L, 2), to_level(L, 3));
    return 0;
}

static int environment_is_ge(lua_State * L) {
    lua_pushboolean(L, to_environment(L, 1).is_ge(to_level(L, 2), to_level(L, 3)));
    return 1;
}

static int environment_get_uvar(lua_State * L) {
    return push_level(L, to_environment(L, 1).get_uvar(to_name_ext(L, 2)));
}

static int environment_add_definition(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3) {
        to_environment(L, 1).add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3));
    } else if (nargs == 4) {
        if (is_expr(L, 4))
            to_environment(L, 1).add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4));
        else
            to_environment(L, 1).add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3), lua_toboolean(L, 4));
    } else {
        to_environment(L, 1).add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4), lua_toboolean(L, 5));
    }
    return 0;
}

static int environment_add_theorem(lua_State * L) {
    to_environment(L, 1).add_theorem(to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4));
    return 0;
}

static int environment_add_var(lua_State * L) {
    to_environment(L, 1).add_var(to_name_ext(L, 2), to_nonnull_expr(L, 3));
    return 0;
}

static int environment_add_axiom(lua_State * L) {
    to_environment(L, 1).add_axiom(to_name_ext(L, 2), to_nonnull_expr(L, 3));
    return 0;
}

static int environment_check_type(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, to_environment(L, 1).infer_type(to_nonnull_expr(L, 2)));
    else
        return push_expr(L, to_environment(L, 1).infer_type(to_nonnull_expr(L, 2), to_context(L, 3)));
}

static int environment_normalize(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, to_environment(L, 1).normalize(to_nonnull_expr(L, 2)));
    else
        return push_expr(L, to_environment(L, 1).normalize(to_nonnull_expr(L, 2), to_context(L, 3)));
}

static int environment_pred(lua_State * L) {
    lua_pushboolean(L, is_environment(L, 1));
    return 1;
}

static const struct luaL_Reg environment_m[] = {
    {"__gc",           environment_gc}, // never throws
    {"add_uvar",       safe_function<environment_add_uvar>},
    {"is_ge",          safe_function<environment_is_ge>},
    {"get_uvar",       safe_function<environment_get_uvar>},
    {"add_definition", safe_function<environment_add_definition>},
    {"add_theorem",    safe_function<environment_add_theorem>},
    {"add_var",        safe_function<environment_add_var>},
    {"add_axiom",      safe_function<environment_add_axiom>},
    {"check_type",     safe_function<environment_check_type>},
    {"normalize",      safe_function<environment_normalize>},
    {0, 0}
};

static char g_set_environment_key;

set_environment::set_environment(lua_State * L, environment & env) {
    m_state = L;
    lua_pushlightuserdata(m_state, (void *)&g_set_environment_key);
    push_environment(m_state, env);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

set_environment::~set_environment() {
    lua_pushlightuserdata(m_state, (void *)&g_set_environment_key);
    lua_pushnil(m_state);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

int get_environment(lua_State * L) {
    lua_pushlightuserdata(L, (void *)&g_set_environment_key);
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!is_environment(L, -1))
        luaL_error(L, "Lua registry does not contain a Lean environment");
    return push_environment(L, to_environment(L, -1));
}

void open_environment(lua_State * L) {
    luaL_newmetatable(L, environment_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, environment_m, 0);

    set_global_function<mk_environment>(L, "environment");
    set_global_function<environment_pred>(L, "is_environment");
    set_global_function<get_environment>(L, "get_environment");
    set_global_function<get_environment>(L, "env");
}
}
