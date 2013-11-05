/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <sstream>
#include <lua.hpp>
#include "util/debug.h"
#include "util/sexpr/sexpr.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/numerics.h"

namespace lean {
constexpr char const * sexpr_mt = "sexpr.mt";

static int push_sexpr(lua_State * L, sexpr const & e) {
    void * mem = lua_newuserdata(L, sizeof(sexpr));
    new (mem) sexpr(e);
    luaL_getmetatable(L, sexpr_mt);
    lua_setmetatable(L, -2);
    return 1;
}

bool is_sexpr(lua_State * L, int idx) {
    return testudata(L, idx, sexpr_mt);
}

static sexpr to_sexpr(lua_State * L, int idx) {
    if (lua_isnil(L, idx)) {
        return sexpr();
    } else if (lua_isboolean(L, idx)) {
        return sexpr(lua_toboolean(L, idx));
    } else if (lua_isnumber(L, idx)) {
        // Remark: we convert to integer by default
        return sexpr(static_cast<int>(lua_tointeger(L, idx)));
    } else if (is_name(L, idx)) {
        return sexpr(to_name(L, idx));
    } else if (is_sexpr(L, idx)) {
        return *static_cast<sexpr*>(lua_touserdata(L, idx));
    } else if (is_mpz(L, idx)) {
        return sexpr(to_mpz(L, idx));
    } else if (is_mpq(L, idx)) {
        return sexpr(to_mpq(L, idx));
    } else {
        return sexpr(lua_tostring(L, idx));
    }
}

static int sexpr_gc(lua_State * L) {
    to_sexpr(L, 1).~sexpr();
    return 0;
}

static int sexpr_tostring(lua_State * L) {
    std::ostringstream out;
    out << to_sexpr(L, 1);
    lua_pushfstring(L, out.str().c_str());
    return 1;
}

static int mk_sexpr(lua_State * L) {
    sexpr r;
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        r = sexpr();
    } else {
        int i = nargs;
        r = to_sexpr(L, i);
        i--;
        for (; i >= 1; i--) {
            r = sexpr(to_sexpr(L, i), r);
        }
    }
    return push_sexpr(L, r);
}

static int sexpr_eq(lua_State * L) {
    lua_pushboolean(L, to_sexpr(L, 1) == to_sexpr(L, 2));
    return 1;
}

static int sexpr_lt(lua_State * L) {
    lua_pushboolean(L, to_sexpr(L, 1) < to_sexpr(L, 2));
    return 1;
}

static const struct luaL_Reg sexpr_m[] = {
    {"__gc",       sexpr_gc}, // never throws
    {"__tostring", safe_function<sexpr_tostring>},
    {"__eq",       safe_function<sexpr_eq>},
    {"__lt",       safe_function<sexpr_lt>},
    {0, 0}
};

void open_sexpr(lua_State * L) {
    luaL_newmetatable(L, sexpr_mt);
    setfuncs(L, sexpr_m, 0);
    lua_pushcfunction(L, safe_function<mk_sexpr>);
    lua_setglobal(L, "sexpr");
}
}
#endif
