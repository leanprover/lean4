/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "util/buffer.h"
#include "kernel/level.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"

namespace lean {
constexpr char const * level_mt = "level.mt";

bool is_level(lua_State * L, int idx) {
    return testudata(L, idx, level_mt);
}

level & to_level(lua_State * L, int idx) {
    return *static_cast<level*>(luaL_checkudata(L, idx, level_mt));
}

int push_level(lua_State * L, level const & e) {
    void * mem = lua_newuserdata(L, sizeof(level));
    new (mem) level(e);
    luaL_getmetatable(L, level_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int level_gc(lua_State * L) {
    to_level(L, 1).~level();
    return 0;
}

static int level_tostring(lua_State * L) {
    std::ostringstream out;
    // TODO(Leo): use pretty printer
    out << to_level(L, 1);
    lua_pushfstring(L, out.str().c_str());
    return 1;
}

static int level_eq(lua_State * L) {
    lua_pushboolean(L, to_level(L, 1) == to_level(L, 2));
    return 1;
}

static int level_lt(lua_State * L) {
    lua_pushboolean(L, to_level(L, 1) < to_level(L, 2));
    return 1;
}

static int mk_level(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        // bottom
        return push_level(L, level());
    } else if (nargs == 1) {
        // uvar
        return push_level(L, level(to_name_ext(L, 1)));
    } else if (nargs == 2 && lua_isnumber(L, 2)) {
        // lift
        return push_level(L, to_level(L, 1) + luaL_checkinteger(L, 2));
    } else {
        // max
        level r = to_level(L, 1);
        for (int i = 2; i <= nargs; i++) {
            r = max(r, to_level(L, i));
        }
        return push_level(L, r);
    }
}

static int level_is_bottom(lua_State * L) {
    lua_pushboolean(L, to_level(L, 1).is_bottom());
    return 1;
}

static int level_is_uvar(lua_State * L) {
    lua_pushboolean(L, is_uvar(to_level(L, 1)));
    return 1;
}

static int level_is_lift(lua_State * L) {
    lua_pushboolean(L, is_lift(to_level(L, 1)));
    return 1;
}

static int level_is_max(lua_State * L) {
    lua_pushboolean(L, is_max(to_level(L, 1)));
    return 1;
}

static int level_name(lua_State * L) {
    if (!is_uvar(to_level(L, 1)))
        throw exception("arg #1 must be a Lean level universal variable");
    return push_name(L, uvar_name(to_level(L, 1)));
}

static int level_lift_of(lua_State * L) {
    if (!is_lift(to_level(L, 1)))
        throw exception("arg #1 must be a Lean level lift");
    return push_level(L, lift_of(to_level(L, 1)));
}

static int level_lift_offset(lua_State * L) {
    if (!is_lift(to_level(L, 1)))
        throw exception("arg #1 must be a Lean level lift");
    lua_pushinteger(L, lift_offset(to_level(L, 1)));
    return 1;
}

static int level_max_size(lua_State * L) {
    if (!is_max(to_level(L, 1)))
        throw exception("arg #1 must be a Lean level max");
    lua_pushinteger(L, max_size(to_level(L, 1)));
    return 1;
}

static int level_max_level(lua_State * L) {
    if (!is_max(to_level(L, 1)))
        throw exception("arg #1 must be a Lean level max");
    return push_level(L, max_level(to_level(L, 1), luaL_checkinteger(L, 2)));
}

static int level_pred(lua_State * L) {
    lua_pushboolean(L, is_level(L, 1));
    return 1;
}

static const struct luaL_Reg level_m[] = {
    {"__gc",            level_gc}, // never throws
    {"__tostring",      safe_function<level_tostring>},
    {"__eq",            safe_function<level_eq>},
    {"__lt",            safe_function<level_lt>},
    {0, 0}
};

void open_level(lua_State * L) {
    luaL_newmetatable(L, level_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, level_m, 0);

    set_global_function<mk_level>(L, "level");
    set_global_function<level_pred>(L, "is_level");
    set_global_function<level_is_bottom>(L, "is_bottom");
    set_global_function<level_is_lift>(L, "is_lift");
    set_global_function<level_is_max>(L, "is_max");
    set_global_function<level_is_uvar>(L, "is_uvar");
    set_global_function<level_name>(L, "uvar_name");
    set_global_function<level_lift_of>(L, "lift_of");
    set_global_function<level_lift_offset>(L, "lift_offset");
    set_global_function<level_max_size>(L, "max_size");
    set_global_function<level_max_level>(L, "max_level");
}
}
