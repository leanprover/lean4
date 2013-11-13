/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "util/sexpr/options.h"
#include "kernel/context.h"
#include "kernel/formatter.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/options.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/formatter.h"

namespace lean {
constexpr char const * context_entry_mt = "context_entry.mt";

bool is_context_entry(lua_State * L, int idx) {
    return testudata(L, idx, context_entry_mt);
}

context_entry & to_context_entry(lua_State * L, int idx) {
    return *static_cast<context_entry*>(luaL_checkudata(L, idx, context_entry_mt));
}

int push_context_entry(lua_State * L, context_entry const & e) {
    void * mem = lua_newuserdata(L, sizeof(context_entry));
    new (mem) context_entry(e);
    luaL_getmetatable(L, context_entry_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int context_entry_gc(lua_State * L) {
    to_context_entry(L, 1).~context_entry();
    return 0;
}

static int mk_context_entry(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_context_entry(L, context_entry(to_name_ext(L, 1), to_nonnull_expr(L, 2)));
    else
        return push_context_entry(L, context_entry(to_name_ext(L, 1), to_nonnull_expr(L, 2), to_nonnull_expr(L, 3)));
}

static int context_entry_pred(lua_State * L) {
    lua_pushboolean(L, is_context_entry(L, 1));
    return 1;
}

static int context_entry_get_name(lua_State * L) { return push_name(L, to_context_entry(L, 1).get_name()); }
static int context_entry_get_domain(lua_State * L) { return push_expr(L, to_context_entry(L, 1).get_domain()); }
static int context_entry_get_body(lua_State * L) { return push_expr(L, to_context_entry(L, 1).get_body()); }

static const struct luaL_Reg context_entry_m[] = {
    {"__gc",            context_entry_gc}, // never throws
    {"get_name",        safe_function<context_entry_get_name>},
    {"get_domain",      safe_function<context_entry_get_domain>},
    {"get_body",        safe_function<context_entry_get_body>},
    {0, 0}
};

constexpr char const * context_mt = "context.mt";

bool is_context(lua_State * L, int idx) {
    return testudata(L, idx, context_mt);
}

context & to_context(lua_State * L, int idx) {
    return *static_cast<context*>(luaL_checkudata(L, idx, context_mt));
}

int push_context(lua_State * L, context const & e) {
    void * mem = lua_newuserdata(L, sizeof(context));
    new (mem) context(e);
    luaL_getmetatable(L, context_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int context_gc(lua_State * L) {
    to_context(L, 1).~context();
    return 0;
}

static int context_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(fmt(to_context(L, 1), opts), opts);
    lua_pushfstring(L, out.str().c_str());
    return 1;
}

static int mk_context(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_context(L, context());
    } else if (nargs == 2) {
        context_entry & e = to_context_entry(L, 2);
        return push_context(L, context(to_context(L, 1), e.get_name(), e.get_domain(), e.get_body()));
    } else if (nargs == 3) {
        return push_context(L, context(to_context(L, 1), to_name_ext(L, 2), to_nonnull_expr(L, 3)));
    } else {
        return push_context(L, context(to_context(L, 1), to_name_ext(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4)));
    }
}

static int context_pred(lua_State * L) {
    lua_pushboolean(L, is_context(L, 1));
    return 1;
}

static int context_extend(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs != 3 && nargs != 4)
        throw exception("extend expect 3 or 4 arguments");
    return mk_context(L);
}

static int context_is_empty(lua_State * L) {
    lua_pushboolean(L, empty(to_context(L, 1)));
    return 1;
}

static int context_lookup(lua_State * L) {
    auto p = lookup_ext(to_context(L, 1), luaL_checkinteger(L, 2));
    push_context_entry(L, p.first);
    push_context(L, p.second);
    return 2;
}

static int context_size(lua_State * L) {
    lua_pushinteger(L, to_context(L, 1).size());
    return 1;
}

static const struct luaL_Reg context_m[] = {
    {"__gc",            context_gc}, // never throws
    {"__tostring",      safe_function<context_tostring>},
    {"__len",           safe_function<context_size>},
    {"is_empty",        safe_function<context_is_empty>},
    {"size",            safe_function<context_size>},
    {"extend",          safe_function<context_extend>},
    {"lookup",          safe_function<context_lookup>},
    {0, 0}
};

void open_context(lua_State * L) {
    luaL_newmetatable(L, context_entry_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, context_entry_m, 0);
    SET_GLOBAL_FUN(mk_context_entry,   "context_entry");
    SET_GLOBAL_FUN(context_entry_pred, "is_context_entry");

    luaL_newmetatable(L, context_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, context_m, 0);
    SET_GLOBAL_FUN(mk_context,     "context");
    SET_GLOBAL_FUN(context_pred,   "is_context");
    SET_GLOBAL_FUN(context_extend, "extend");
    SET_GLOBAL_FUN(context_lookup, "lookup");
}
}
