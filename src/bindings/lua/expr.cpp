/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_LUA
#include <sstream>
#include <lua.hpp>
#include <utility>
#include "util/debug.h"
#include "util/name.h"
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/abstract.h"
#include "library/expr_lt.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"

namespace lean {
constexpr char const * expr_mt = "expr.mt";

bool is_expr(lua_State * L, int idx) {
    return testudata(L, idx, expr_mt);
}

expr & to_expr(lua_State * L, int idx) {
    return *static_cast<expr*>(luaL_checkudata(L, idx, expr_mt));
}

int push_expr(lua_State * L, expr const & e) {
    void * mem = lua_newuserdata(L, sizeof(expr));
    new (mem) expr(e);
    luaL_getmetatable(L, expr_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int expr_gc(lua_State * L) {
    to_expr(L, 1).~expr();
    return 0;
}

static int expr_tostring(lua_State * L) {
    std::ostringstream out;
    // TODO(Leo): use pretty printer
    out << to_expr(L, 1);
    lua_pushfstring(L, out.str().c_str());
    return 1;
}

static int expr_eq(lua_State * L) {
    lua_pushboolean(L, to_expr(L, 1) == to_expr(L, 2));
    return 1;
}

static int expr_lt(lua_State * L) {
    lua_pushboolean(L, to_expr(L, 1) < to_expr(L, 2));
    return 1;
}

static int expr_mk_constant(lua_State * L) {
    return push_expr(L, mk_constant(to_name_ext(L, 1)));
}

static int expr_mk_var(lua_State * L) {
    return push_expr(L, mk_var(luaL_checkinteger(L, 1)));
}

static int expr_mk_app(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs < 2)
        luaL_error(L, "application must have at least two arguments");
    buffer<expr> args;
    for (int i = 1; i <= nargs; i++)
        args.push_back(to_expr(L, i));
    return push_expr(L, mk_app(args));
}

static int expr_mk_eq(lua_State * L) {
    return push_expr(L, mk_eq(to_expr(L, 1), to_expr(L, 2)));
}

static int expr_mk_lambda(lua_State * L) {
    return push_expr(L, mk_lambda(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
}

static int expr_mk_pi(lua_State * L) {
    return push_expr(L, mk_lambda(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
}

static int expr_mk_let(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3)
        return push_expr(L, mk_let(to_name_ext(L, 1), expr(), to_expr(L, 2), to_expr(L, 3)));
    else
        return push_expr(L, mk_let(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3), to_expr(L, 4)));
}

static expr get_expr_from_table(lua_State * L, int t, int i) {
    lua_pushvalue(L, t); // push table to the top
    lua_pushinteger(L, i);
    lua_gettable(L, -2);
    expr r = to_expr(L, -1);
    lua_pop(L, 2); // remove table and value
    return r;
}

// t is a table of pairs {{a1, b1}, ..., {ak, bk}}
// Each ai and bi is an expression
static std::pair<expr, expr> get_expr_pair_from_table(lua_State * L, int t, int i) {
    lua_pushvalue(L, t); // push table on the top
    lua_pushinteger(L, i);
    lua_gettable(L, -2); // now table {ai, bi} is on the top
    if (!lua_istable(L, -1) || objlen(L, -1) != 2)
        luaL_error(L, "arg #1 must be of the form '{{expr, expr}, ...}'");
    expr ai = get_expr_from_table(L, -1, 1);
    expr bi = get_expr_from_table(L, -1, 2);
    lua_pop(L, 2); // pop table {ai, bi} and t from stack
    return mk_pair(ai, bi);
}

static int expr_fun(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs < 2)
        luaL_error(L, "Lean fun must have at least 2 arguments");
    if (nargs == 2) {
        if (!lua_istable(L, 1))
            luaL_error(L, "Lean fun expects arg #1 to be of the form '{{expr, expr}, ...}'");
        int len = objlen(L, 1);
        if (len == 0)
            luaL_error(L, "Lean fun expects arg #1 to be non-empty table");
        expr r = to_expr(L, 2);
        for (int i = len; i >= 1; i--) {
            auto p = get_expr_pair_from_table(L, 1, i);
            r = Fun(p.first, p.second, r);
        }
        return push_expr(L, r);
    } else {
        if (nargs % 2 == 0)
            luaL_error(L, "Lean fun must have an odd number of arguments");
        expr r = to_expr(L, nargs);
        for (int i = nargs - 1; i >= 1; i-=2) {
            if (is_expr(L, i - 1))
                r = Fun(to_expr(L, i - 1), to_expr(L, i), r);
            else
                r = Fun(to_name_ext(L, i - 1), to_expr(L, i), r);
        }
        return push_expr(L, r);
    }
}

static int expr_pi(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs < 2)
        luaL_error(L, "Lean Pi must have at least 2 arguments");
    if (nargs == 2) {
        if (!lua_istable(L, 1))
            luaL_error(L, "Lean Pi expects arg #1 to be of the form '{{expr, expr}, ...}'");
        int len = objlen(L, 1);
        if (len == 0)
            luaL_error(L, "Lean Pi expects arg #1 to be non-empty table");
        expr r = to_expr(L, 2);
        for (int i = len; i >= 1; i--) {
            auto p = get_expr_pair_from_table(L, 1, i);
            r = Pi(p.first, p.second, r);
        }
        return push_expr(L, r);
    } else {
        if (nargs % 2 == 0)
            luaL_error(L, "Lean Pi must have an odd number of arguments");
        expr r = to_expr(L, nargs);
        for (int i = nargs - 1; i >= 1; i-=2) {
            if (is_expr(L, i - 1))
                r = Pi(to_expr(L, i - 1), to_expr(L, i), r);
            else
                r = Pi(to_name_ext(L, i - 1), to_expr(L, i), r);
        }
        return push_expr(L, r);
    }
}

static const struct luaL_Reg expr_m[] = {
    {"__gc",       expr_gc}, // never throws
    {"__tostring", safe_function<expr_tostring>},
    {"__eq",       safe_function<expr_eq>},
    {"__lt",       safe_function<expr_lt>},
    {"__call",     safe_function<expr_mk_app>},
    {0, 0}
};

void open_expr(lua_State * L) {
    luaL_newmetatable(L, expr_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, expr_m, 0);

    set_global_function<expr_mk_constant>(L, "mk_constant");
    set_global_function<expr_mk_constant>(L, "Const");
    set_global_function<expr_mk_var>(L, "mk_var");
    set_global_function<expr_mk_var>(L, "Var");
    set_global_function<expr_mk_app>(L, "mk_app");
    set_global_function<expr_mk_eq>(L, "mk_eq");
    set_global_function<expr_mk_eq>(L, "Eq");
    set_global_function<expr_mk_lambda>(L, "mk_lambda");
    set_global_function<expr_mk_pi>(L, "mk_pi");
    set_global_function<expr_mk_let>(L, "mk_let");
    set_global_function<expr_fun>(L, "fun");
    set_global_function<expr_fun>(L, "Fun");
    set_global_function<expr_pi>(L, "Pi");
}
}
#endif
