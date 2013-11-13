/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "util/buffer.h"
#include "util/sexpr/options.h"
#include "kernel/level.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/options.h"

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
    options opts  = get_global_options(L);
    out << mk_pair(pp(to_level(L, 1), opts), opts);
    lua_pushstring(L, out.str().c_str());
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

#define LEVEL_PRED(P)                           \
static int level_ ## P(lua_State * L)    {      \
    lua_pushboolean(L, P(to_level(L, 1)));      \
    return 1;                                   \
}

LEVEL_PRED(is_bottom)
LEVEL_PRED(is_uvar)
LEVEL_PRED(is_lift)
LEVEL_PRED(is_max)

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

static int level_get_kind(lua_State * L) {
    lua_pushinteger(L, static_cast<int>(kind(to_level(L, 1))));
    return 1;
}

static const struct luaL_Reg level_m[] = {
    {"__gc",            level_gc}, // never throws
    {"__tostring",      safe_function<level_tostring>},
    {"__eq",            safe_function<level_eq>},
    {"__lt",            safe_function<level_lt>},
    {"kind",            safe_function<level_get_kind>},
    {"is_bottom",       safe_function<level_is_bottom>},
    {"is_lift",         safe_function<level_is_lift>},
    {"is_max",          safe_function<level_is_max>},
    {"is_uvar",         safe_function<level_is_uvar>},
    {"uvar_name",       safe_function<level_name>},
    {"lift_of",         safe_function<level_lift_of>},
    {"lift_offset",     safe_function<level_lift_offset>},
    {"max_size",        safe_function<level_max_size>},
    {"max_level",       safe_function<level_max_level>},
    {0, 0}
};

void open_level(lua_State * L) {
    luaL_newmetatable(L, level_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, level_m, 0);

    SET_GLOBAL_FUN(mk_level,   "level");
    SET_GLOBAL_FUN(level_pred, "is_level");

    lua_newtable(L);
    SET_ENUM("UVar",      level_kind::UVar);
    SET_ENUM("Lift",      level_kind::Lift);
    SET_ENUM("Max",       level_kind::Max);
    lua_setglobal(L, "level_kind");
}
}
