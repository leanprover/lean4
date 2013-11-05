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

int push_sexpr(lua_State * L, sexpr const & e) {
    void * mem = lua_newuserdata(L, sizeof(sexpr));
    new (mem) sexpr(e);
    luaL_getmetatable(L, sexpr_mt);
    lua_setmetatable(L, -2);
    return 1;
}

bool is_sexpr(lua_State * L, int idx) {
    return testudata(L, idx, sexpr_mt);
}

sexpr & to_sexpr(lua_State * L, int idx) {
    return *static_cast<sexpr*>(lua_touserdata(L, idx));
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

static sexpr to_sexpr_elem(lua_State * L, int idx) {
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

static int mk_sexpr(lua_State * L) {
    sexpr r;
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        r = sexpr();
    } else {
        int i = nargs;
        r = to_sexpr_elem(L, i);
        i--;
        for (; i >= 1; i--) {
            r = sexpr(to_sexpr_elem(L, i), r);
        }
    }
    return push_sexpr(L, r);
}

static int sexpr_eq(lua_State * L)        { lua_pushboolean(L, to_sexpr(L, 1) == to_sexpr(L, 2));  return 1; }
static int sexpr_lt(lua_State * L)        { lua_pushboolean(L, to_sexpr(L, 1) < to_sexpr(L, 2));   return 1; }
static int sexpr_is_nil(lua_State * L)    { lua_pushboolean(L, is_nil(to_sexpr(L, 1)));            return 1; }
static int sexpr_is_cons(lua_State * L)   { lua_pushboolean(L, is_cons(to_sexpr(L, 1)));           return 1; }
static int sexpr_is_list(lua_State * L)   { lua_pushboolean(L, is_list(to_sexpr(L, 1)));           return 1; }
static int sexpr_is_atom(lua_State * L)   { lua_pushboolean(L, is_atom(to_sexpr(L, 1)));           return 1; }
static int sexpr_is_string(lua_State * L) { lua_pushboolean(L, is_string(to_sexpr(L, 1)));         return 1; }
static int sexpr_is_bool(lua_State * L)   { lua_pushboolean(L, is_bool(to_sexpr(L, 1)));           return 1; }
static int sexpr_is_int(lua_State * L)    { lua_pushboolean(L, is_int(to_sexpr(L, 1)));            return 1; }
static int sexpr_is_double(lua_State * L) { lua_pushboolean(L, is_double(to_sexpr(L, 1)));         return 1; }
static int sexpr_is_name(lua_State * L)   { lua_pushboolean(L, is_name(to_sexpr(L, 1)));           return 1; }
static int sexpr_is_mpz(lua_State * L)    { lua_pushboolean(L, is_mpz(to_sexpr(L, 1)));            return 1; }
static int sexpr_is_mpq(lua_State * L)    { lua_pushboolean(L, is_mpq(to_sexpr(L, 1)));            return 1; }

static int sexpr_length(lua_State * L)    {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_list(e))
        return luaL_error(L, "s-expression is not a list");
    lua_pushinteger(L, length(e));
    return 1;
}

static int sexpr_head(lua_State * L)      {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_cons(e))
        return luaL_error(L, "s-expression is not a cons cell");
    return push_sexpr(L, head(e));
}

static int sexpr_tail(lua_State * L)      {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_cons(e))
        return luaL_error(L, "s-expression is not a cons cell");
    return push_sexpr(L, tail(e));
}

static int sexpr_to_bool(lua_State * L)   { lua_pushboolean(L, to_bool(to_sexpr(L, 1)));           return 1; }
static int sexpr_to_string(lua_State * L) { lua_pushfstring(L, to_string(to_sexpr(L, 1)).c_str()); return 1; }
static int sexpr_to_int(lua_State * L)    { lua_pushinteger(L, to_int(to_sexpr(L, 1)));            return 1; }
static int sexpr_to_double(lua_State * L) { lua_pushnumber(L, to_double(to_sexpr(L, 1)));          return 1; }
static int sexpr_to_name(lua_State * L)   { return push_name(L, to_name(to_sexpr(L, 1))); }
static int sexpr_to_mpz(lua_State * L)    { return push_mpz(L, to_mpz(to_sexpr(L, 1))); }
static int sexpr_to_mpq(lua_State * L)    { return push_mpq(L, to_mpq(to_sexpr(L, 1))); }

static const struct luaL_Reg sexpr_m[] = {
    {"__gc",       sexpr_gc}, // never throws
    {"__tostring", safe_function<sexpr_tostring>},
    {"__eq",       safe_function<sexpr_eq>},
    {"__lt",       safe_function<sexpr_lt>},
    {"is_nil",     safe_function<sexpr_is_nil>},
    {"is_cons",    safe_function<sexpr_is_cons>},
    {"is_list",    safe_function<sexpr_is_list>},
    {"is_atom",    safe_function<sexpr_is_atom>},
    {"is_string",  safe_function<sexpr_is_string>},
    {"is_bool",    safe_function<sexpr_is_bool>},
    {"is_int",     safe_function<sexpr_is_int>},
    {"is_double",  safe_function<sexpr_is_double>},
    {"is_name",    safe_function<sexpr_is_name>},
    {"is_mpz",     safe_function<sexpr_is_mpz>},
    {"is_mpq",     safe_function<sexpr_is_mpq>},
    {"head",       safe_function<sexpr_head>},
    {"tail",       safe_function<sexpr_tail>},
    {"length",     safe_function<sexpr_length>},
    {"to_bool",    safe_function<sexpr_to_bool>},
    {"to_string",  safe_function<sexpr_to_string>},
    {"to_int",     safe_function<sexpr_to_int>},
    {"to_double",  safe_function<sexpr_to_double>},
    {"to_name",    safe_function<sexpr_to_name>},
    {"to_mpz",     safe_function<sexpr_to_mpz>},
    {"to_mpq",     safe_function<sexpr_to_mpq>},
    {0, 0}
};

void open_sexpr(lua_State * L) {
    luaL_newmetatable(L, sexpr_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, sexpr_m, 0);
    lua_pushcfunction(L, safe_function<mk_sexpr>);
    lua_setglobal(L, "sexpr");
}
}
#endif
