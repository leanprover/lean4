/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
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
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static sexpr to_sexpr_elem(lua_State * L, int idx) {
    if (lua_isnil(L, idx)) {
        return sexpr();
    } else if (lua_isboolean(L, idx)) {
        return sexpr(static_cast<bool>(lua_toboolean(L, idx)));
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

#define SEXPR_PRED(P)                           \
static int sexpr_ ## P(lua_State * L)    {      \
    lua_pushboolean(L, P(to_sexpr(L, 1)));      \
    return 1;                                   \
}

SEXPR_PRED(is_nil)
SEXPR_PRED(is_cons)
SEXPR_PRED(is_list)
SEXPR_PRED(is_atom)
SEXPR_PRED(is_string)
SEXPR_PRED(is_bool)
SEXPR_PRED(is_int)
SEXPR_PRED(is_double)
SEXPR_PRED(is_name)
SEXPR_PRED(is_mpz)
SEXPR_PRED(is_mpq)

static int sexpr_length(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_list(e))
        throw exception("s-expression is not a list");
    lua_pushinteger(L, length(e));
    return 1;
}

static int sexpr_head(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_cons(e))
        throw exception("s-expression is not a cons cell");
    return push_sexpr(L, head(e));
}

static int sexpr_tail(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_cons(e))
        throw exception("s-expression is not a cons cell");
    return push_sexpr(L, tail(e));
}

static int sexpr_to_bool(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_bool(e))
        throw exception("s-expression is not a Boolean");
    lua_pushboolean(L, to_bool(e));
    return 1;
}

static int sexpr_to_string(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_string(e))
        throw exception("s-expression is not a string");
    lua_pushstring(L, to_string(e).c_str());
    return 1;
}

static int sexpr_to_int(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_int(e))
        throw exception("s-expression is not an integer");
    lua_pushinteger(L, to_int(e));
    return 1;
}

static int sexpr_to_double(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_double(e))
        throw exception("s-expression is not a double");
    lua_pushnumber(L, to_double(e));
    return 1;
}

static int sexpr_to_name(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_name(e))
        throw exception("s-expression is not a name");
    return push_name(L, to_name(e));
}

static int sexpr_to_mpz(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_mpz(e))
        throw exception("s-expression is not a multi-precision integer");
    return push_mpz(L, to_mpz(e));
}

static int sexpr_to_mpq(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_mpq(e))
        throw exception("s-expression is not a multi-precision rational");
    return push_mpq(L, to_mpq(e));
}

static int sexpr_pred(lua_State * L) {
    lua_pushboolean(L, is_sexpr(L, 1));
    return 1;
}

static int sexpr_get_kind(lua_State * L) {
    lua_pushinteger(L, static_cast<int>(to_sexpr(L, 1).kind()));
    return 1;
}

static int sexpr_fields(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    switch (e.kind()) {
    case sexpr_kind::Nil:         return 0;
    case sexpr_kind::String:      return sexpr_to_string(L);
    case sexpr_kind::Bool:        return sexpr_to_bool(L);
    case sexpr_kind::Int:         return sexpr_to_int(L);
    case sexpr_kind::Double:      return sexpr_to_double(L);
    case sexpr_kind::Name:        return sexpr_to_name(L);
    case sexpr_kind::MPZ:         return sexpr_to_mpz(L);
    case sexpr_kind::MPQ:         return sexpr_to_mpq(L);
    case sexpr_kind::Cons:        sexpr_head(L); sexpr_tail(L); return 2;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
    return 0;           // LCOV_EXCL_LINE
}

static const struct luaL_Reg sexpr_m[] = {
    {"__gc",       sexpr_gc}, // never throws
    {"__tostring", safe_function<sexpr_tostring>},
    {"__eq",       safe_function<sexpr_eq>},
    {"__lt",       safe_function<sexpr_lt>},
    {"kind",       safe_function<sexpr_get_kind>},
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
    {"fields",     safe_function<sexpr_fields>},
    {0, 0}
};

void open_sexpr(lua_State * L) {
    luaL_newmetatable(L, sexpr_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, sexpr_m, 0);

    SET_GLOBAL_FUN(mk_sexpr,   "sexpr");
    SET_GLOBAL_FUN(sexpr_pred, "is_sexpr");

    lua_newtable(L);
    SET_ENUM("Nil",         sexpr_kind::Nil);
    SET_ENUM("String",      sexpr_kind::String);
    SET_ENUM("Bool",        sexpr_kind::Bool);
    SET_ENUM("Int",         sexpr_kind::Int);
    SET_ENUM("Double",      sexpr_kind::Double);
    SET_ENUM("Name",        sexpr_kind::Name);
    SET_ENUM("MPZ",         sexpr_kind::MPZ);
    SET_ENUM("MPQ",         sexpr_kind::MPQ);
    SET_ENUM("Cons",        sexpr_kind::Cons);
    lua_setglobal(L, "sexpr_kind");
}
}
