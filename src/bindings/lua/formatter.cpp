/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "kernel/formatter.h"
#include "bindings/lua/util.h"
#include "bindings/lua/options.h"
#include "bindings/lua/format.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/environment.h"
#include "bindings/lua/object.h"
#include "bindings/lua/io_state.h"

namespace lean {
DECL_UDATA(formatter)

[[ noreturn ]] void throw_invalid_formatter_call() {
    throw exception("invalid formatter invocation, the acceptable arguments are: (expr, options?), (context, options?), (context, expr, bool? options?), (kernel object, options?), (environment, options?)");
}

static int formatter_call(lua_State * L) {
    int nargs = lua_gettop(L);
    formatter & fmt = to_formatter(L, 1);
    options opts = get_global_options(L);
    if (nargs <= 3) {
        if (nargs == 3) {
            if (is_options(L, 3))
                opts = to_options(L, 3);
            else if (is_context(L, 2) && is_expr(L, 3))
                return push_format(L, fmt(to_context(L, 2), to_expr(L, 3)));
            else
                throw_invalid_formatter_call();
        }
        if (is_expr(L, 2))  {
            return push_format(L, fmt(to_expr(L, 2), opts));
        } else if (is_context(L, 2)) {
            return push_format(L, fmt(to_context(L, 2), opts));
        } else if (is_environment(L, 2)) {
            ro_environment env(L, 2);
            return push_format(L, fmt(env, opts));
        } else if (is_object(L, 2)) {
            return push_format(L, fmt(to_object(L, 2), opts));
        } else {
            throw_invalid_formatter_call();
        }
    } else if (nargs <= 5) {
        if (nargs == 5)
            opts = to_options(L, 5);
        return push_format(L, fmt(to_context(L, 2), to_expr(L, 3), lua_toboolean(L, 4), opts));
    } else {
        throw_invalid_formatter_call();
    }
}

static const struct luaL_Reg formatter_m[] = {
    {"__gc",            formatter_gc}, // never throws
    {"__call",          safe_function<formatter_call>},
    {0, 0}
};

static char g_formatter_key;
static formatter g_simple_formatter = mk_simple_formatter();

formatter get_global_formatter(lua_State * L) {
    io_state * io = get_io_state(L);
    if (io != nullptr) {
        return io->get_formatter();
    } else {
        lua_pushlightuserdata(L, static_cast<void *>(&g_formatter_key));
        lua_gettable(L, LUA_REGISTRYINDEX);
        if (is_formatter(L, -1)) {
            formatter r = to_formatter(L, -1);
            lua_pop(L, 1);
            return r;
        } else {
            lua_pop(L, 1);
            return g_simple_formatter;
        }
    }
}

void set_global_formatter(lua_State * L, formatter const & fmt) {
    io_state * io = get_io_state(L);
    if (io != nullptr) {
        io->set_formatter(fmt);
    } else {
        lua_pushlightuserdata(L, static_cast<void *>(&g_formatter_key));
        push_formatter(L, fmt);
        lua_settable(L, LUA_REGISTRYINDEX);
    }
}

int get_formatter(lua_State * L) {
    return push_formatter(L, get_global_formatter(L));
}

void open_formatter(lua_State * L) {
    luaL_newmetatable(L, formatter_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, formatter_m, 0);

    SET_GLOBAL_FUN(formatter_pred, "is_formatter");
    SET_GLOBAL_FUN(get_formatter,  "get_formatter");
}
}
