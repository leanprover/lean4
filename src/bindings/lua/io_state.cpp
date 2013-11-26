/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lua.hpp>
#include "library/io_state.h"
#include "bindings/lua/util.h"
#include "bindings/lua/io_state.h"
#include "bindings/lua/options.h"
#include "bindings/lua/formatter.h"

namespace lean {
DECL_UDATA(io_state)

int mk_io_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_io_state(L, io_state());
    else if (nargs == 1)
        return push_io_state(L, io_state(to_io_state(L, 1)));
    else
        return push_io_state(L, io_state(to_options(L, 1), to_formatter(L, 2)));
}

int io_state_get_options(lua_State * L) {
    return push_options(L, to_io_state(L, 1).get_options());
}

int io_state_get_formatter(lua_State * L) {
    return push_formatter(L, to_io_state(L, 1).get_formatter());
}

int io_state_set_options(lua_State * L) {
    to_io_state(L, 1).set_options(to_options(L, 2));
    return 0;
}

int print(lua_State * L, io_state & ios, int start, bool reg);

int io_state_print_regular(lua_State * L) {
    return print(L, to_io_state(L, 1), 2, true);
}

int io_state_print_diagnostic(lua_State * L) {
    return print(L, to_io_state(L, 1), 2, false);
}

static const struct luaL_Reg io_state_m[] = {
    {"__gc",             io_state_gc}, // never throws
    {"get_options",      safe_function<io_state_get_options>},
    {"set_options",      safe_function<io_state_set_options>},
    {"get_formatter",    safe_function<io_state_get_formatter>},
    {"print_diagnostic", safe_function<io_state_print_diagnostic>},
    {"print_regular",    safe_function<io_state_print_regular>},
    {"print",            safe_function<io_state_print_regular>},
    {"diagnostic",       safe_function<io_state_print_diagnostic>},
    {0, 0}
};

void open_io_state(lua_State * L) {
    luaL_newmetatable(L, io_state_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, io_state_m, 0);

    SET_GLOBAL_FUN(io_state_pred, "is_io_state");
    SET_GLOBAL_FUN(mk_io_state, "io_state");
}

static char g_set_state_key;

set_io_state::set_io_state(lua_State * L, io_state & st) {
    m_state = L;
    m_prev  = get_io_state(L);
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(m_state, &st);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

set_io_state::~set_io_state() {
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(m_state, m_prev);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

io_state * get_io_state(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_state_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!lua_islightuserdata(L, -1)) {
        lua_pop(L, 1);
        return nullptr;
    } else {
        io_state * r = static_cast<io_state*>(lua_touserdata(L, -1));
        lua_pop(L, 1);
        return r;
    }
}
}
