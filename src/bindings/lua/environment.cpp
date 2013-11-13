/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "kernel/environment.h"
#include "kernel/formatter.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/options.h"
#include "bindings/lua/level.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/object.h"
#include "bindings/lua/context.h"
#include "bindings/lua/environment.h"
#include "bindings/lua/formatter.h"

namespace lean {
constexpr char const * environment_mt = "environment.mt";

bool is_environment(lua_State * L, int idx) {
    return testudata(L, idx, environment_mt);
}

environment & to_environment(lua_State * L, int idx) {
    return *static_cast<environment*>(luaL_checkudata(L, idx, environment_mt));
}

ro_environment::ro_environment(lua_State * L, int idx):
    read_only_environment(to_environment(L, idx)) {
}

rw_environment::rw_environment(lua_State * L, int idx):
    read_write_environment(to_environment(L, idx)) {
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

static int environment_has_parent(lua_State * L) {
    ro_environment env(L, 1);
    lua_pushboolean(L, env->has_parent());
    return 1;
}

static int environment_has_children(lua_State * L) {
    ro_environment env(L, 1);
    lua_pushboolean(L, env->has_children());
    return 1;
}

static int environment_parent(lua_State * L) {
    ro_environment env(L, 1);
    if (!env->has_parent())
        throw exception("environment does not have a parent environment");
    return push_environment(L, env->parent());
}

static int environment_add_uvar(lua_State * L) {
    rw_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 2)
        env->add_uvar(to_name_ext(L, 2));
    else
        env->add_uvar(to_name_ext(L, 2), to_level(L, 3));
    return 0;
}

static int environment_is_ge(lua_State * L) {
    ro_environment env(L, 1);
    lua_pushboolean(L, env->is_ge(to_level(L, 2), to_level(L, 3)));
    return 1;
}

static int environment_get_uvar(lua_State * L) {
    ro_environment env(L, 1);
    return push_level(L, env->get_uvar(to_name_ext(L, 2)));
}

static int environment_add_definition(lua_State * L) {
    rw_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 3) {
        env->add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3));
    } else if (nargs == 4) {
        if (is_expr(L, 4))
            env->add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4));
        else
            env->add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3), lua_toboolean(L, 4));
    } else {
        env->add_definition(to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4), lua_toboolean(L, 5));
    }
    return 0;
}

static int environment_add_theorem(lua_State * L) {
    rw_environment env(L, 1);
    env->add_theorem(to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4));
    return 0;
}

static int environment_add_var(lua_State * L) {
    rw_environment env(L, 1);
    env->add_var(to_name_ext(L, 2), to_nonnull_expr(L, 3));
    return 0;
}

static int environment_add_axiom(lua_State * L) {
    rw_environment env(L, 1);
    env->add_axiom(to_name_ext(L, 2), to_nonnull_expr(L, 3));
    return 0;
}

static int environment_find_object(lua_State * L) {
    ro_environment env(L, 1);
    return push_object(L, env->find_object(to_name_ext(L, 2)));
}

static int environment_has_object(lua_State * L) {
    ro_environment env(L, 1);
    lua_pushboolean(L, env->has_object(to_name_ext(L, 2)));
    return 1;
}

static int environment_check_type(lua_State * L) {
    ro_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, env->infer_type(to_nonnull_expr(L, 2)));
    else
        return push_expr(L, env->infer_type(to_nonnull_expr(L, 2), to_context(L, 3)));
}

static int environment_normalize(lua_State * L) {
    ro_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, env->normalize(to_nonnull_expr(L, 2)));
    else
        return push_expr(L, env->normalize(to_nonnull_expr(L, 2), to_context(L, 3)));
}

static int environment_objects(lua_State * L) {
    ro_environment env(L, 1);
    auto it  = env->begin_objects();
    auto end = env->end_objects();
    lua_newtable(L);
    for (int i = 1; it != end; ++it, ++i) {
        push_object(L, *it);
        lua_rawseti(L, -2, i);
    }
    return 1;
}

static int environment_local_objects(lua_State * L) {
    ro_environment env(L, 1);
    auto it  = env->begin_local_objects();
    auto end = env->end_local_objects();
    lua_newtable(L);
    for (int i = 1; it != end; ++it, ++i) {
        push_object(L, *it);
        lua_rawseti(L, -2, i);
    }
    return 1;
}

static int environment_pred(lua_State * L) {
    lua_pushboolean(L, is_environment(L, 1));
    return 1;
}

static int environment_tostring(lua_State * L) {
    ro_environment env(L, 1);
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(fmt(env, opts), opts);
    lua_pushfstring(L, out.str().c_str());
    return 1;
}

static const struct luaL_Reg environment_m[] = {
    {"__gc",           environment_gc}, // never throws
    {"__tostring",     safe_function<environment_tostring>},
    {"has_parent",     safe_function<environment_has_parent>},
    {"has_children",   safe_function<environment_has_children>},
    {"parent",         safe_function<environment_parent>},
    {"add_uvar",       safe_function<environment_add_uvar>},
    {"is_ge",          safe_function<environment_is_ge>},
    {"get_uvar",       safe_function<environment_get_uvar>},
    {"add_definition", safe_function<environment_add_definition>},
    {"add_theorem",    safe_function<environment_add_theorem>},
    {"add_var",        safe_function<environment_add_var>},
    {"add_axiom",      safe_function<environment_add_axiom>},
    {"find_object",    safe_function<environment_find_object>},
    {"has_object",     safe_function<environment_has_object>},
    {"check_type",     safe_function<environment_check_type>},
    {"normalize",      safe_function<environment_normalize>},
    {"objects",        safe_function<environment_objects>},
    {"local_objects",  safe_function<environment_local_objects>},
    {0, 0}
};

static char g_set_environment_key;

set_environment::set_environment(lua_State * L, environment & env) {
    m_state = L;
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_environment_key));
    push_environment(m_state, env);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

set_environment::~set_environment() {
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_environment_key));
    lua_pushnil(m_state);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

int get_environment(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_environment_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!is_environment(L, -1))
        throw exception("Lua registry does not contain a Lean environment");
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
