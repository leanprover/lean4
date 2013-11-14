/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include <utility>
#include "util/debug.h"
#include "util/name.h"
#include "util/buffer.h"
#include "util/sexpr/options.h"
#include "kernel/expr.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/formatter.h"
#include "kernel/for_each.h"
#include "kernel/free_vars.h"
#include "kernel/occurs.h"
#include "kernel/metavar.h"
#include "library/expr_lt.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/options.h"
#include "bindings/lua/level.h"
#include "bindings/lua/local_context.h"
#include "bindings/lua/formatter.h"

namespace lean {
constexpr char const * expr_mt = "expr.mt";

bool is_expr(lua_State * L, int idx) {
    return testudata(L, idx, expr_mt);
}

expr & to_expr(lua_State * L, int idx) {
    return *static_cast<expr*>(luaL_checkudata(L, idx, expr_mt));
}

expr & to_nonnull_expr(lua_State * L, int idx) {
    expr & r = to_expr(L, idx);
    if (!r)
        throw exception("non-null Lean expression expected");
    return r;
}

expr & to_app(lua_State * L, int idx) {
    expr & r = to_nonnull_expr(L, idx);
    if (!is_app(r))
        throw exception("Lean application expression expected");
    return r;
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
    expr & e = to_expr(L, 1);
    if (e) {
        formatter fmt = get_global_formatter(L);
        options opts  = get_global_options(L);
        out << mk_pair(fmt(to_expr(L, 1), opts), opts);
    } else {
        out << "<null-expr>";
    }
    lua_pushstring(L, out.str().c_str());
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
        throw exception("application must have at least two arguments");
    buffer<expr> args;
    for (int i = 1; i <= nargs; i++)
        args.push_back(to_nonnull_expr(L, i));
    return push_expr(L, mk_app(args));
}

static int expr_mk_eq(lua_State * L) {
    return push_expr(L, mk_eq(to_nonnull_expr(L, 1), to_nonnull_expr(L, 2)));
}

static int expr_mk_lambda(lua_State * L) {
    return push_expr(L, mk_lambda(to_name_ext(L, 1), to_nonnull_expr(L, 2), to_nonnull_expr(L, 3)));
}

static int expr_mk_pi(lua_State * L) {
    return push_expr(L, mk_pi(to_name_ext(L, 1), to_nonnull_expr(L, 2), to_nonnull_expr(L, 3)));
}

static int expr_mk_arrow(lua_State * L) {
    return push_expr(L, mk_arrow(to_nonnull_expr(L, 1), to_nonnull_expr(L, 2)));
}

static int expr_mk_let(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3)
        return push_expr(L, mk_let(to_name_ext(L, 1), expr(), to_nonnull_expr(L, 2), to_nonnull_expr(L, 3)));
    else
        return push_expr(L, mk_let(to_name_ext(L, 1), to_nonnull_expr(L, 2), to_nonnull_expr(L, 3), to_nonnull_expr(L, 4)));
}

static expr get_expr_from_table(lua_State * L, int t, int i) {
    lua_pushvalue(L, t); // push table to the top
    lua_pushinteger(L, i);
    lua_gettable(L, -2);
    expr r = to_nonnull_expr(L, -1);
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
        throw exception("arg #1 must be of the form '{{expr, expr}, ...}'");
    expr ai = get_expr_from_table(L, -1, 1);
    expr bi = get_expr_from_table(L, -1, 2);
    lua_pop(L, 2); // pop table {ai, bi} and t from stack
    return mk_pair(ai, bi);
}

typedef expr (*MkAbst1)(expr const & n, expr const & t, expr const & b);
typedef expr (*MkAbst2)(name const & n, expr const & t, expr const & b);

template<MkAbst1 F1, MkAbst2 F2>
int expr_abst(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs < 2)
        throw exception("function must have at least 2 arguments");
    if (nargs == 2) {
        if (!lua_istable(L, 1))
            throw exception("function expects arg #1 to be of the form '{{expr, expr}, ...}'");
        int len = objlen(L, 1);
        if (len == 0)
            throw exception("function expects arg #1 to be a non-empty table");
        expr r = to_nonnull_expr(L, 2);
        for (int i = len; i >= 1; i--) {
            auto p = get_expr_pair_from_table(L, 1, i);
            r = F1(p.first, p.second, r);
        }
        return push_expr(L, r);
    } else {
        if (nargs % 2 == 0)
            throw exception("function must have an odd number of arguments");
        expr r = to_nonnull_expr(L, nargs);
        for (int i = nargs - 1; i >= 1; i-=2) {
            if (is_expr(L, i - 1))
                r = F1(to_nonnull_expr(L, i - 1), to_nonnull_expr(L, i), r);
            else
                r = F2(to_name_ext(L, i - 1), to_nonnull_expr(L, i), r);
        }
        return push_expr(L, r);
    }
}

static int expr_fun(lua_State * L) { return expr_abst<Fun, Fun>(L); }
static int expr_pi(lua_State * L)  { return expr_abst<Pi, Pi>(L); }
static int expr_let(lua_State * L) { return expr_abst<Let, Let>(L); }

static int expr_type(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_expr(L, Type());
    else
        return push_expr(L, Type(to_level(L, 1)));
}

static int expr_mk_metavar(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_expr(L, mk_metavar(to_name_ext(L, 1)));
    else
        return push_expr(L, mk_metavar(to_name_ext(L, 1), to_local_context(L, 2)));
}

static int expr_is_null(lua_State * L) {
    lua_pushboolean(L, !to_expr(L, 1));
    return 1;
}

static int expr_get_kind(lua_State * L) {
    lua_pushinteger(L, static_cast<int>(to_nonnull_expr(L, 1).kind()));
    return 1;
}

#define EXPR_PRED(P)                                    \
static int expr_ ## P(lua_State * L) {                  \
    lua_pushboolean(L, P(to_nonnull_expr(L, 1)));       \
    return 1;                                           \
}

EXPR_PRED(is_constant)
EXPR_PRED(is_var)
EXPR_PRED(is_app)
EXPR_PRED(is_eq)
EXPR_PRED(is_lambda)
EXPR_PRED(is_pi)
EXPR_PRED(is_abstraction)
EXPR_PRED(is_let)
EXPR_PRED(is_value)
EXPR_PRED(is_metavar)
EXPR_PRED(has_free_vars)
EXPR_PRED(closed)
EXPR_PRED(has_metavar)

/**
   \brief Iterator (closure base function) for application args. See \c expr_args
*/
static int expr_next_arg(lua_State * L) {
    expr & e   = to_expr(L, lua_upvalueindex(1));
    unsigned i = lua_tointeger(L, lua_upvalueindex(2));
    if (i >= num_args(e)) {
        lua_pushnil(L);
    } else {
        lua_pushinteger(L, i + 1);
        lua_replace(L, lua_upvalueindex(2)); // update closure
        push_expr(L, arg(e, i));
    }
    return 1;
}

static int expr_args(lua_State * L) {
    expr & e = to_app(L, 1);
    push_expr(L, e);         // upvalue(1): expr
    lua_pushinteger(L, 0);   // upvalue(2): index
    lua_pushcclosure(L, &expr_next_arg, 2); // create closure with 2 upvalues
    return 1;
}

static int expr_num_args(lua_State * L) {
    lua_pushinteger(L, num_args(to_app(L, 1)));
    return 1;
}

static int expr_arg(lua_State * L) {
    return push_expr(L, arg(to_app(L, 1), luaL_checkinteger(L, 2)));
}

static int expr_fields(lua_State * L) {
    expr & e = to_nonnull_expr(L, 1);
    switch (e.kind()) {
    case expr_kind::Var:      lua_pushinteger(L, var_idx(e)); return 1;
    case expr_kind::Constant: return push_name(L, const_name(e));
    case expr_kind::Type:     return push_level(L, ty_level(e));
    case expr_kind::Value:    return 0;
    case expr_kind::App:      lua_pushinteger(L, num_args(e)); expr_args(L); return 2;
    case expr_kind::Eq:       push_expr(L, eq_lhs(e)); push_expr(L, eq_rhs(e)); return 2;
    case expr_kind::Lambda:
    case expr_kind::Pi:       push_name(L, abst_name(e)); push_expr(L, abst_domain(e)); push_expr(L, abst_body(e)); return 3;
    case expr_kind::Let:      push_name(L, let_name(e));  push_expr(L, let_type(e)); push_expr(L, let_value(e)); push_expr(L, let_body(e)); return 4;
    case expr_kind::MetaVar:  push_name(L, metavar_name(e)); push_local_context(L, metavar_lctx(e)); return 2;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
    return 0;           // LCOV_EXCL_LINE
}

static int expr_pred(lua_State * L) {
    lua_pushboolean(L, is_expr(L, 1));
    return 1;
}

static int expr_for_each(lua_State * L) {
    expr & e = to_nonnull_expr(L, 1);    // expr
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    auto f = [&](expr const & a, unsigned offset) {
        lua_pushvalue(L, 2); // push user-fun
        push_expr(L, a);
        lua_pushinteger(L, offset);
        pcall(L, 2, 1, 0);
        bool r = true;
        if (lua_isboolean(L, -1))
            r = lua_toboolean(L, -1);
        lua_pop(L, 1);
        return r;
    };
    for_each_fn<decltype(f)> proc(f);
    proc(e);
    return 0;
}

static int expr_has_free_var(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        lua_pushboolean(L, has_free_var(to_expr(L, 1), luaL_checkinteger(L, 2)));
    else
        lua_pushboolean(L, has_free_var(to_expr(L, 1), luaL_checkinteger(L, 2), luaL_checkinteger(L, 3)));
    return 1;
}

static int expr_lift_free_vars(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, lift_free_vars(to_expr(L, 1), luaL_checkinteger(L, 2)));
    else
        return push_expr(L, lift_free_vars(to_expr(L, 1), luaL_checkinteger(L, 2), luaL_checkinteger(L, 3)));
}

static int expr_lower_free_vars(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, lower_free_vars(to_expr(L, 1), luaL_checkinteger(L, 2)));
    else
        return push_expr(L, lower_free_vars(to_expr(L, 1), luaL_checkinteger(L, 2), luaL_checkinteger(L, 3)));
}

// Copy Lua table/array elements to r
static void copy_lua_array(lua_State * L, int tidx, buffer<expr> & r) {
    luaL_checktype(L, tidx, LUA_TTABLE);
    int n = objlen(L, tidx);
    for (int i = 1; i <= n; i++) {
        lua_rawgeti(L, tidx, i);
        r.push_back(to_expr(L, -1));
        lua_pop(L, 1);
    }
}

static int expr_instantiate(lua_State * L) {
    expr const & e = to_expr(L, 1);
    if (is_expr(L, 2)) {
        return push_expr(L, instantiate(e, to_expr(L, 2)));
    } else {
        buffer<expr> s;
        copy_lua_array(L, 2, s);
        return push_expr(L, instantiate(e, s.size(), s.data()));
    }
}

static int expr_abstract(lua_State * L) {
    expr const & e = to_expr(L, 1);
    if (is_expr(L, 2)) {
        expr const & e2 = to_expr(L, 2);
        return push_expr(L, abstract(e, 1, &e2));
    } else {
        buffer<expr> s;
        copy_lua_array(L, 2, s);
        return push_expr(L, abstract(e, s.size(), s.data()));
    }
}

static int expr_occurs(lua_State * L) {
    lua_pushboolean(L, occurs(to_expr(L, 1), to_expr(L, 2)));
    return 1;
}

static int expr_is_eqp(lua_State * L) {
    lua_pushboolean(L, is_eqp(to_expr(L, 1), to_expr(L, 2)));
    return 1;
}

static int expr_hash(lua_State * L) {
    lua_pushinteger(L, to_expr(L, 1).hash());
    return 1;
}

static const struct luaL_Reg expr_m[] = {
    {"__gc",            expr_gc}, // never throws
    {"__tostring",      safe_function<expr_tostring>},
    {"__eq",            safe_function<expr_eq>},
    {"__lt",            safe_function<expr_lt>},
    {"__call",          safe_function<expr_mk_app>},
    {"kind",            safe_function<expr_get_kind>},
    {"is_null",         safe_function<expr_is_null>},
    {"is_var",          safe_function<expr_is_var>},
    {"is_constant",     safe_function<expr_is_constant>},
    {"is_app",          safe_function<expr_is_app>},
    {"is_eq",           safe_function<expr_is_eq>},
    {"is_lambda",       safe_function<expr_is_lambda>},
    {"is_pi",           safe_function<expr_is_pi>},
    {"is_abstraction",  safe_function<expr_is_abstraction>},
    {"is_let",          safe_function<expr_is_let>},
    {"is_value",        safe_function<expr_is_value>},
    {"is_metavar",      safe_function<expr_is_metavar>},
    {"fields",          safe_function<expr_fields>},
    {"args",            safe_function<expr_args>},
    {"num_args",        safe_function<expr_num_args>},
    {"arg",             safe_function<expr_arg>},
    {"for_each",        safe_function<expr_for_each>},
    {"has_free_vars",   safe_function<expr_has_free_vars>},
    {"closed",          safe_function<expr_closed>},
    {"has_free_var",    safe_function<expr_has_free_var>},
    {"lift_free_vars",  safe_function<expr_lift_free_vars>},
    {"lower_free_vars", safe_function<expr_lower_free_vars>},
    {"instantiate",     safe_function<expr_instantiate>},
    {"abstract",        safe_function<expr_abstract>},
    {"occurs",          safe_function<expr_occurs>},
    {"has_metavar",     safe_function<expr_has_metavar>},
    {"is_eqp",          safe_function<expr_is_eqp>},
    {"hash",            safe_function<expr_hash>},
    {0, 0}
};

void open_expr(lua_State * L) {
    luaL_newmetatable(L, expr_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, expr_m, 0);

    SET_GLOBAL_FUN(expr_mk_constant, "mk_constant");
    SET_GLOBAL_FUN(expr_mk_constant, "Const");
    SET_GLOBAL_FUN(expr_mk_var,      "mk_var");
    SET_GLOBAL_FUN(expr_mk_var,      "Var");
    SET_GLOBAL_FUN(expr_mk_app,      "mk_app");
    SET_GLOBAL_FUN(expr_mk_eq,       "mk_eq");
    SET_GLOBAL_FUN(expr_mk_eq,       "Eq");
    SET_GLOBAL_FUN(expr_mk_lambda,        "mk_lambda");
    SET_GLOBAL_FUN(expr_mk_pi,       "mk_pi");
    SET_GLOBAL_FUN(expr_mk_arrow,    "mk_arrow");
    SET_GLOBAL_FUN(expr_mk_let,      "mk_let");
    SET_GLOBAL_FUN(expr_fun,         "fun");
    SET_GLOBAL_FUN(expr_fun,         "Fun");
    SET_GLOBAL_FUN(expr_pi,          "Pi");
    SET_GLOBAL_FUN(expr_let,         "Let");
    SET_GLOBAL_FUN(expr_type,        "mk_type");
    SET_GLOBAL_FUN(expr_type,        "Type");
    SET_GLOBAL_FUN(expr_mk_metavar,  "mk_metavar");
    SET_GLOBAL_FUN(expr_pred,        "is_expr");

    lua_newtable(L);
    SET_ENUM("Var",      expr_kind::Var);
    SET_ENUM("Constant", expr_kind::Constant);
    SET_ENUM("Type",     expr_kind::Type);
    SET_ENUM("Value",    expr_kind::Value);
    SET_ENUM("App",      expr_kind::App);
    SET_ENUM("Eq",       expr_kind::Eq);
    SET_ENUM("Lambda",   expr_kind::Lambda);
    SET_ENUM("Pi",       expr_kind::Pi);
    SET_ENUM("Let",      expr_kind::Let);
    SET_ENUM("MetaVar",  expr_kind::MetaVar);
    lua_setglobal(L, "expr_kind");
}
}
