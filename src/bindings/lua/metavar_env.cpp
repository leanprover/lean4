/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
#include "util/sstream.h"
#include "kernel/metavar.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/justification.h"

namespace lean {
DECL_UDATA(metavar_env)

static int menv_mk_metavar(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1) {
        return push_expr(L, to_metavar_env(L, 1).mk_metavar());
    } else if (nargs == 2) {
        return push_expr(L, to_metavar_env(L, 1).mk_metavar(to_context(L, 2)));
    } else {
        return push_expr(L, to_metavar_env(L, 1).mk_metavar(to_context(L, 2), to_expr(L, 3)));
    }
}

static expr & to_metavar(lua_State * L, int i, bool lctx = true) {
    expr & e = to_expr(L, i);
    if (is_metavar(e)) {
        if (lctx || !has_local_context(e))
            return e;
        throw exception(sstream() << "arg #" << i << " must be a metavariable without a local context");
    }
    throw exception(sstream() << "arg #" << i << " must be a metavariable");
}

static int menv_get_timestamp(lua_State * L) {
    lua_pushinteger(L, to_metavar_env(L, 1).get_timestamp());
    return 1;
}

static int menv_get_context(lua_State * L) {
    if (is_expr(L, 2))
        return push_context(L, to_metavar_env(L, 1).get_context(to_metavar(L, 2, false)));
    else
        return push_context(L, to_metavar_env(L, 1).get_context(to_name_ext(L, 2)));
}

static int menv_has_type(lua_State * L) {
    if (is_expr(L, 2))
        lua_pushboolean(L, to_metavar_env(L, 1).has_type(to_metavar(L, 2)));
    else
        lua_pushboolean(L, to_metavar_env(L, 1).has_type(to_name_ext(L, 2)));
    return 1;
}

static int menv_get_type(lua_State * L) {
    if (is_expr(L, 2))
        return push_expr(L, to_metavar_env(L, 1).get_type(to_metavar(L, 2)));
    else
        return push_expr(L, to_metavar_env(L, 1).get_type(to_name_ext(L, 2)));
}

static int menv_is_assigned(lua_State * L) {
    if (is_expr(L, 2))
        lua_pushboolean(L, to_metavar_env(L, 1).is_assigned(to_metavar(L, 2)));
    else
        lua_pushboolean(L, to_metavar_env(L, 1).is_assigned(to_name_ext(L, 2)));
    return 1;
}

static int menv_assign(lua_State * L) {
    int nargs = lua_gettop(L);
    justification jst;
    if (nargs == 4)
        jst = to_justification(L, 4);
    if (is_expr(L, 2))
        to_metavar_env(L, 1).assign(to_metavar(L, 2, false), to_expr(L, 3), jst);
    else
        to_metavar_env(L, 1).assign(to_name_ext(L, 2), to_expr(L, 3), jst);
    return 0;
}

static int menv_get_subst(lua_State * L) {
    if (is_expr(L, 2))
        return push_expr(L, to_metavar_env(L, 1).get_subst(to_metavar(L, 2)));
    else
        return push_expr(L, to_metavar_env(L, 1).get_subst(to_name_ext(L, 2)));
}

static int menv_get_justification(lua_State * L) {
    if (is_expr(L, 2))
        return push_justification(L, to_metavar_env(L, 1).get_justification(to_metavar(L, 2)));
    else
        return push_justification(L, to_metavar_env(L, 1).get_justification(to_name_ext(L, 2)));
}

static int menv_get_subst_jst(lua_State * L) {
    if (is_expr(L, 2)) {
        auto p = to_metavar_env(L, 1).get_subst_jst(to_metavar(L, 2));
        push_expr(L, p.first);
        push_justification(L, p.second);
    } else {
        auto p = to_metavar_env(L, 1).get_subst_jst(to_name_ext(L, 2));
        push_expr(L, p.first);
        push_justification(L, p.second);
    }
    return 2;
}

static int menv_for_each_subst(lua_State * L) {
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    to_metavar_env(L, 1).for_each_subst([&](name const & n, expr const & e) {
            lua_pushvalue(L, 2); // push user-fun
            push_name(L, n);
            push_expr(L, e);
            pcall(L, 2, 0, 0);
        });
    return 0;
}

static int mk_metavar_env(lua_State * L) {
    if (lua_gettop(L) == 1)
        return push_metavar_env(L, metavar_env(to_name_ext(L, 1)));
    else
        return push_metavar_env(L, metavar_env());
}

static int menv_copy(lua_State * L) {
    return push_metavar_env(L, metavar_env(to_metavar_env(L, 1)));
}

static const struct luaL_Reg metavar_env_m[] = {
    {"__gc",              metavar_env_gc}, // never throws
    {"mk_metavar",        safe_function<menv_mk_metavar>},
    {"get_timestamp",     safe_function<menv_get_timestamp>},
    {"get_context",       safe_function<menv_get_context>},
    {"has_type",          safe_function<menv_has_type>},
    {"get_type",          safe_function<menv_get_type>},
    {"is_assigned",       safe_function<menv_is_assigned>},
    {"assign",            safe_function<menv_assign>},
    {"get_subst",         safe_function<menv_get_subst>},
    {"get_justification", safe_function<menv_get_justification>},
    {"get_subt_jst",      safe_function<menv_get_subst_jst>},
    {"for_each_subst",    safe_function<menv_for_each_subst>},
    {"copy",              safe_function<menv_copy>},
    {0, 0}
};

void open_metavar_env(lua_State * L) {
    luaL_newmetatable(L, metavar_env_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, metavar_env_m, 0);

    SET_GLOBAL_FUN(mk_metavar_env,   "metavar_env");
    SET_GLOBAL_FUN(metavar_env_pred, "is_metavar_env");
}
}
