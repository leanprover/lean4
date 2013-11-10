/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "kernel/expr.h"
#include "bindings/lua/util.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/local_context.h"

namespace lean {
constexpr char const * local_entry_mt = "local_entry.mt";

bool is_local_entry(lua_State * L, int idx) {
    return testudata(L, idx, local_entry_mt);
}

local_entry & to_local_entry(lua_State * L, int idx) {
    return *static_cast<local_entry*>(luaL_checkudata(L, idx, local_entry_mt));
}

int push_local_entry(lua_State * L, local_entry const & e) {
    void * mem = lua_newuserdata(L, sizeof(local_entry));
    new (mem) local_entry(e);
    luaL_getmetatable(L, local_entry_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int local_entry_gc(lua_State * L) {
    to_local_entry(L, 1).~local_entry();
    return 0;
}

static int local_entry_eq(lua_State * L) {
    lua_pushboolean(L, to_local_entry(L, 1) == to_local_entry(L, 2));
    return 1;
}

static int local_entry_mk_lift(lua_State * L) {
    return push_local_entry(L, mk_lift(luaL_checkinteger(L, 1), luaL_checkinteger(L, 2)));
}

static int local_entry_mk_inst(lua_State * L) {
    return push_local_entry(L, mk_inst(luaL_checkinteger(L, 1), to_nonnull_expr(L, 2)));
}

static int local_entry_pred(lua_State * L) {
    lua_pushboolean(L, is_local_entry(L, 1));
    return 1;
}

static int local_entry_is_lift(lua_State * L) {
    lua_pushboolean(L, is_local_entry(L, 1) && to_local_entry(L, 1).is_lift());
    return 1;
}

static int local_entry_is_inst(lua_State * L) {
    lua_pushboolean(L, is_local_entry(L, 1) && to_local_entry(L, 1).is_inst());
    return 1;
}

static int local_entry_s(lua_State * L) {
    lua_pushinteger(L, to_local_entry(L, 1).s());
    return 1;
}

static int local_entry_n(lua_State * L) {
    local_entry & e = to_local_entry(L, 1);
    if (!e.is_lift())
        luaL_error(L, "Lean lift local entry expected");
    lua_pushinteger(L, to_local_entry(L, 1).n());
    return 1;
}

static int local_entry_v(lua_State * L) {
    local_entry & e = to_local_entry(L, 1);
    if (!e.is_inst())
        luaL_error(L, "Lean inst local entry expected");
    return push_expr(L, to_local_entry(L, 1).v());
    return 1;
}

static const struct luaL_Reg local_entry_m[] = {
    {"__gc",      local_entry_gc}, // never throws
    {"__eq",      safe_function<local_entry_eq>},
    {"is_lift",   safe_function<local_entry_is_lift>},
    {"is_inst",   safe_function<local_entry_is_inst>},
    {"s",         safe_function<local_entry_s>},
    {"n",         safe_function<local_entry_n>},
    {"v",         safe_function<local_entry_v>},
    {0, 0}
};

constexpr char const * local_context_mt = "local_context.mt";

bool is_local_context(lua_State * L, int idx) {
    return testudata(L, idx, local_context_mt);
}

local_context & to_local_context(lua_State * L, int idx) {
    return *static_cast<local_context*>(luaL_checkudata(L, idx, local_context_mt));
}

int push_local_context(lua_State * L, local_context const & e) {
    void * mem = lua_newuserdata(L, sizeof(local_context));
    new (mem) local_context(e);
    luaL_getmetatable(L, local_context_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int local_context_gc(lua_State * L) {
    to_local_context(L, 1).~local_context();
    return 0;
}

static int mk_local_context(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_local_context(L, local_context());
    } else {
        return push_local_context(L, local_context(to_local_entry(L, 1), to_local_context(L, 2)));
    }
}

static int local_context_head(lua_State * L) {
    return push_local_entry(L, head(to_local_context(L, 1)));
}

static int local_context_tail(lua_State * L) {
    return push_local_context(L, tail(to_local_context(L, 1)));
}

static int local_context_is_nil(lua_State * L) {
    lua_pushboolean(L, !to_local_context(L, 1));
    return 1;
}

static int local_context_pred(lua_State * L) {
    lua_pushboolean(L, is_local_context(L, 1));
    return 1;
}

static const struct luaL_Reg local_context_m[] = {
    {"__gc",      local_context_gc},
    {"head",      local_context_head},
    {"tail",      local_context_tail},
    {"is_nil",    local_context_is_nil},
    {0, 0}
};

void open_local_context(lua_State * L) {
    luaL_newmetatable(L, local_entry_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, local_entry_m, 0);
    set_global_function<local_entry_mk_lift>(L, "mk_lift");
    set_global_function<local_entry_mk_inst>(L, "mk_inst");
    set_global_function<local_entry_pred>(L, "is_local_entry");

    luaL_newmetatable(L, local_context_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, local_context_m, 0);
    set_global_function<mk_local_context>(L, "local_context");
    set_global_function<local_context_pred>(L, "is_local_context");
}
}
