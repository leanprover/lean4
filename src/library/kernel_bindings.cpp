/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/sstream.h"
#include "util/script_state.h"
#include "library/io_state_stream.h"
#include "library/expr_lt.h"
#include "library/kernel_bindings.h"

// Lua Bindings for the Kernel classes. We do not include the Lua
// bindings in the kernel because we do not want to inflate the Kernel.

namespace lean {
DECL_UDATA(level)

static int level_tostring(lua_State * L) {
    std::ostringstream out;
    options opts  = get_global_options(L);
    out << mk_pair(pp(to_level(L, 1), opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int level_eq(lua_State * L) { return pushboolean(L, to_level(L, 1) == to_level(L, 2)); }
static int level_lt(lua_State * L) { return pushboolean(L, is_lt(to_level(L, 1), to_level(L, 2))); }
static int mk_level_zero(lua_State * L) { return push_level(L, mk_level_zero()); }
static int mk_level_one(lua_State * L)  { return push_level(L, mk_level_one());  }
static int mk_level_succ(lua_State * L) { return push_level(L, mk_succ(to_level(L, 1))); }
static int mk_level_max(lua_State * L)  { return push_level(L, mk_max(to_level(L, 1), to_level(L, 2))); }
static int mk_level_imax(lua_State * L) { return push_level(L, mk_imax(to_level(L, 1), to_level(L, 2))); }
static int mk_param_univ(lua_State * L) { return push_level(L, mk_param_univ(to_name_ext(L, 1))); }
static int mk_meta_univ(lua_State * L)  { return push_level(L, mk_meta_univ(to_name_ext(L, 1))); }
#define LEVEL_PRED(P) static int level_ ## P(lua_State * L) { return pushboolean(L, P(to_level(L, 1))); }
LEVEL_PRED(is_zero)
LEVEL_PRED(is_param)
LEVEL_PRED(is_meta)
LEVEL_PRED(is_succ)
LEVEL_PRED(is_max)
LEVEL_PRED(is_imax)
LEVEL_PRED(is_explicit)
LEVEL_PRED(has_meta)
LEVEL_PRED(has_param)
LEVEL_PRED(is_not_zero)
static int level_get_kind(lua_State * L) { return pushinteger(L, static_cast<int>(kind(to_level(L, 1)))); }
static int level_trivially_leq(lua_State * L) { return pushboolean(L, is_trivial(to_level(L, 1), to_level(L, 2))); }

static int level_id(lua_State * L) {
    level const & l = to_level(L, 1);
    if (is_param(l))     return push_name(L, param_id(l));
    else if (is_meta(l)) return push_name(L, meta_id(l));
    else throw exception("arg #1 must be a level parameter/metavariable");
}

static int level_lhs(lua_State * L) {
    level const & l = to_level(L, 1);
    if (is_max(l))       return push_level(L, max_lhs(l));
    else if (is_imax(l)) return push_level(L, imax_lhs(l));
    else throw exception("arg #1 must be a level max/imax expression");
}

static int level_rhs(lua_State * L) {
    level const & l = to_level(L, 1);
    if (is_max(l))       return push_level(L, max_rhs(l));
    else if (is_imax(l)) return push_level(L, imax_rhs(l));
    else throw exception("arg #1 must be a level max/imax expression");
}

static int level_succ_of(lua_State * L) {
    level const & l = to_level(L, 1);
    if (is_succ(l))      return push_level(L, succ_of(l));
    else throw exception("arg #1 must be a level succ expression");
}

static const struct luaL_Reg level_m[] = {
    {"__gc",            level_gc}, // never throws
    {"__tostring",      safe_function<level_tostring>},
    {"__eq",            safe_function<level_eq>},
    {"__lt",            safe_function<level_lt>},
    {"succ",            safe_function<mk_level_succ>},
    {"kind",            safe_function<level_get_kind>},
    {"is_zero",         safe_function<level_is_zero>},
    {"is_param",        safe_function<level_is_param>},
    {"is_meta",         safe_function<level_is_meta>},
    {"is_succ",         safe_function<level_is_succ>},
    {"is_max",          safe_function<level_is_max>},
    {"is_imax",         safe_function<level_is_imax>},
    {"is_explicit",     safe_function<level_is_explicit>},
    {"has_meta",        safe_function<level_has_meta>},
    {"has_param",       safe_function<level_has_param>},
    {"is_not_zero",     safe_function<level_is_not_zero>},
    {"trivially_leq",   safe_function<level_trivially_leq>},
    {"id",              safe_function<level_id>},
    {"lhs",             safe_function<level_lhs>},
    {"rhs",             safe_function<level_rhs>},
    {"succ_of",         safe_function<level_succ_of>},
    {0, 0}
};

static void open_level(lua_State * L) {
    luaL_newmetatable(L, level_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, level_m, 0);

    SET_GLOBAL_FUN(mk_level_zero,  "level");
    SET_GLOBAL_FUN(mk_level_zero,  "mk_level_zero");
    SET_GLOBAL_FUN(mk_level_one,   "mk_level_one");
    SET_GLOBAL_FUN(mk_level_succ,  "mk_level_succ");
    SET_GLOBAL_FUN(mk_level_max,   "mk_level_max");
    SET_GLOBAL_FUN(mk_level_imax,  "mk_level_imax");
    SET_GLOBAL_FUN(mk_param_univ,  "mk_param_univ");
    SET_GLOBAL_FUN(mk_meta_univ,   "mk_meta_univ");

    SET_GLOBAL_FUN(level_pred, "is_level");

    lua_newtable(L);
    SET_ENUM("Zero",      level_kind::Zero);
    SET_ENUM("Succ",      level_kind::Succ);
    SET_ENUM("Max",       level_kind::Max);
    SET_ENUM("IMax",      level_kind::IMax);
    SET_ENUM("Param",     level_kind::Param);
    SET_ENUM("Meta",      level_kind::Meta);
    lua_setglobal(L, "level_kind");
}

void open_kernel_module(lua_State * L) {
    // TODO(Leo)
    open_level(L);
}
}

#if 0
namespace lean {

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


DECL_UDATA(expr)

int push_optional_expr(lua_State * L, optional<expr> const & e) {
    if (e)
        push_expr(L, *e);
    else
        lua_pushnil(L);
    return 1;
}

expr & to_app(lua_State * L, int idx) {
    expr & r = to_expr(L, idx);
    if (!is_app(r))
        throw exception("Lean application expression expected");
    return r;
}

static int expr_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(fmt(to_expr(L, 1), opts), opts);
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
        args.push_back(to_expr(L, i));
    return push_expr(L, mk_app(args));
}

static int expr_mk_lambda(lua_State * L) {
    return push_expr(L, mk_lambda(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
}

static int expr_mk_pi(lua_State * L) {
    return push_expr(L, mk_pi(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
}

static int expr_mk_arrow(lua_State * L) {
    return push_expr(L, mk_arrow(to_expr(L, 1), to_expr(L, 2)));
}

static int expr_mk_let(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3)
        return push_expr(L, mk_let(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
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
        expr r = to_expr(L, 2);
        for (int i = len; i >= 1; i--) {
            auto p = get_expr_pair_from_table(L, 1, i);
            r = F1(p.first, p.second, r);
        }
        return push_expr(L, r);
    } else {
        if (nargs % 2 == 0)
            throw exception("function must have an odd number of arguments");
        expr r = to_expr(L, nargs);
        for (int i = nargs - 1; i >= 1; i-=2) {
            if (is_expr(L, i - 1))
                r = F1(to_expr(L, i - 1), to_expr(L, i), r);
            else
                r = F2(to_name_ext(L, i - 1), to_expr(L, i), r);
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

static int expr_get_kind(lua_State * L) {
    lua_pushinteger(L, static_cast<int>(to_expr(L, 1).kind()));
    return 1;
}

#define EXPR_PRED(P)                                    \
static int expr_ ## P(lua_State * L) {                  \
    lua_pushboolean(L, P(to_expr(L, 1)));       \
    return 1;                                           \
}

EXPR_PRED(is_constant)
EXPR_PRED(is_var)
EXPR_PRED(is_app)
EXPR_PRED(is_lambda)
EXPR_PRED(is_pi)
EXPR_PRED(is_abstraction)
EXPR_PRED(is_let)
EXPR_PRED(is_value)
EXPR_PRED(is_metavar)
EXPR_PRED(has_free_vars)
EXPR_PRED(closed)
EXPR_PRED(has_metavar)
EXPR_PRED(is_not)
EXPR_PRED(is_and)
EXPR_PRED(is_or)
EXPR_PRED(is_implies)
EXPR_PRED(is_exists)
EXPR_PRED(is_eq)

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
    lua_pushcclosure(L, &safe_function<expr_next_arg>, 2); // create closure with 2 upvalues
    return 1;
}

static int expr_num_args(lua_State * L) {
    lua_pushinteger(L, num_args(to_app(L, 1)));
    return 1;
}

static int expr_arg(lua_State * L) {
    expr & e = to_app(L, 1);
    int i    = luaL_checkinteger(L, 2);
    if (i >= static_cast<int>(num_args(e)) || i < 0)
        throw exception(sstream() << "invalid application argument #" << i << ", application has " << num_args(e) << " arguments");
    return push_expr(L, arg(e, i));
}

static int expr_fields(lua_State * L) {
    expr & e = to_expr(L, 1);
    switch (e.kind()) {
    case expr_kind::Var:      lua_pushinteger(L, var_idx(e)); return 1;
    case expr_kind::Constant: return push_name(L, const_name(e));
    case expr_kind::Type:     return push_level(L, ty_level(e));
    case expr_kind::Value:    return to_value(e).push_lua(L);
    case expr_kind::App:      lua_pushinteger(L, num_args(e)); expr_args(L); return 2;
    case expr_kind::HEq:      push_expr(L, heq_lhs(e)); push_expr(L, heq_rhs(e)); return 3;
    case expr_kind::Pair:     push_expr(L, pair_first(e)); push_expr(L, pair_second(e)); push_expr(L, pair_type(e)); return 3;
    case expr_kind::Proj:     lua_pushboolean(L, proj_first(e)); push_expr(L, proj_arg(e)); return 2;
    case expr_kind::Lambda:
    case expr_kind::Pi:
    case expr_kind::Sigma:
        push_name(L, abst_name(e)); push_expr(L, abst_domain(e)); push_expr(L, abst_body(e)); return 3;
    case expr_kind::Let:
        push_name(L, let_name(e));  push_optional_expr(L, let_type(e)); push_expr(L, let_value(e)); push_expr(L, let_body(e)); return 4;
    case expr_kind::MetaVar:  push_name(L, metavar_name(e)); push_local_context(L, metavar_lctx(e)); return 2;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
    return 0;           // LCOV_EXCL_LINE
}

static int expr_for_each(lua_State * L) {
    expr & e = to_expr(L, 1);    // expr
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

static int expr_head_beta_reduce(lua_State * L) {
    return push_expr(L, head_beta_reduce(to_expr(L, 1)));
}

static int expr_beta_reduce(lua_State * L) {
    return push_expr(L, beta_reduce(to_expr(L, 1)));
}

static void check_abstraction(lua_State * L, int idx, char const * msg) {
    if (!is_abstraction(to_expr(L, idx)))
        throw exception(msg);
}

static int expr_abst_name(lua_State * L) {
    check_abstraction(L, 1, "invalid abst_name call, expression is not an abstraction");
    return push_name(L, abst_name(to_expr(L, 1)));
}

static int expr_abst_domain(lua_State * L) {
    check_abstraction(L, 1, "invalid abst_domain call, expression is not an abstraction");
    return push_expr(L, abst_domain(to_expr(L, 1)));
}

static int expr_abst_body(lua_State * L) {
    check_abstraction(L, 1, "invalid abst_body call, expression is not an abstraction");
    return push_expr(L, abst_body(to_expr(L, 1)));
}

static int expr_mk_eq(lua_State * L) {
    return push_expr(L, mk_eq(to_expr(L, 1), to_expr(L, 2), to_expr(L, 3)));
}

static int expr_depth(lua_State * L) {
    lua_pushinteger(L, get_depth(to_expr(L, 1)));
    return 1;
}

static int expr_is_lt(lua_State * L) {
    lua_pushboolean(L, is_lt(to_expr(L, 1), to_expr(L, 2), false));
    return 1;
}

static const struct luaL_Reg expr_m[] = {
    {"__gc",             expr_gc}, // never throws
    {"__tostring",       safe_function<expr_tostring>},
    {"__eq",             safe_function<expr_eq>},
    {"__lt",             safe_function<expr_lt>},
    {"__call",           safe_function<expr_mk_app>},
    {"kind",             safe_function<expr_get_kind>},
    {"is_var",           safe_function<expr_is_var>},
    {"is_constant",      safe_function<expr_is_constant>},
    {"is_app",           safe_function<expr_is_app>},
    {"is_lambda",        safe_function<expr_is_lambda>},
    {"is_pi",            safe_function<expr_is_pi>},
    {"is_abstraction",   safe_function<expr_is_abstraction>},
    {"is_let",           safe_function<expr_is_let>},
    {"is_value",         safe_function<expr_is_value>},
    {"is_metavar",       safe_function<expr_is_metavar>},
    {"fields",           safe_function<expr_fields>},
    {"data",             safe_function<expr_fields>},
    {"args",             safe_function<expr_args>},
    {"num_args",         safe_function<expr_num_args>},
    {"depth",            safe_function<expr_depth>},
    {"arg",              safe_function<expr_arg>},
    {"abst_name",        safe_function<expr_abst_name>},
    {"abst_domain",      safe_function<expr_abst_domain>},
    {"abst_body",        safe_function<expr_abst_body>},
    {"for_each",         safe_function<expr_for_each>},
    {"has_free_vars",    safe_function<expr_has_free_vars>},
    {"closed",           safe_function<expr_closed>},
    {"has_free_var",     safe_function<expr_has_free_var>},
    {"lift_free_vars",   safe_function<expr_lift_free_vars>},
    {"lower_free_vars",  safe_function<expr_lower_free_vars>},
    {"instantiate",      safe_function<expr_instantiate>},
    {"beta_reduce",      safe_function<expr_beta_reduce>},
    {"head_beta_reduce", safe_function<expr_head_beta_reduce>},
    {"abstract",         safe_function<expr_abstract>},
    {"occurs",           safe_function<expr_occurs>},
    {"has_metavar",      safe_function<expr_has_metavar>},
    {"is_eqp",           safe_function<expr_is_eqp>},
    {"is_lt",            safe_function<expr_is_lt>},
    {"hash",             safe_function<expr_hash>},
    {"is_not",           safe_function<expr_is_not>},
    {"is_and",           safe_function<expr_is_and>},
    {"is_or",            safe_function<expr_is_or>},
    {"is_implies",       safe_function<expr_is_implies>},
    {"is_exists",        safe_function<expr_is_exists>},
    {"is_eq",            safe_function<expr_is_eq>},
    {0, 0}
};

static void expr_migrate(lua_State * src, int i, lua_State * tgt) {
    push_expr(tgt, to_expr(src, i));
}

static void open_expr(lua_State * L) {
    luaL_newmetatable(L, expr_mt);
    set_migrate_fn_field(L, -1, expr_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, expr_m, 0);

    SET_GLOBAL_FUN(expr_mk_constant, "mk_constant");
    SET_GLOBAL_FUN(expr_mk_constant, "Const");
    SET_GLOBAL_FUN(expr_mk_var,      "mk_var");
    SET_GLOBAL_FUN(expr_mk_var,      "Var");
    SET_GLOBAL_FUN(expr_mk_app,      "mk_app");
    SET_GLOBAL_FUN(expr_mk_lambda,   "mk_lambda");
    SET_GLOBAL_FUN(expr_mk_pi,       "mk_pi");
    SET_GLOBAL_FUN(expr_mk_arrow,    "mk_arrow");
    SET_GLOBAL_FUN(expr_mk_let,      "mk_let");
    SET_GLOBAL_FUN(expr_fun,         "fun");
    SET_GLOBAL_FUN(expr_fun,         "Fun");
    SET_GLOBAL_FUN(expr_pi,          "Pi");
    SET_GLOBAL_FUN(expr_let,         "Let");
    SET_GLOBAL_FUN(expr_type,        "mk_type");
    SET_GLOBAL_FUN(expr_mk_eq,       "mk_eq");
    SET_GLOBAL_FUN(expr_type,        "Type");
    SET_GLOBAL_FUN(expr_mk_metavar,  "mk_metavar");
    SET_GLOBAL_FUN(expr_pred,        "is_expr");

    lua_newtable(L);
    SET_ENUM("Var",      expr_kind::Var);
    SET_ENUM("Constant", expr_kind::Constant);
    SET_ENUM("Type",     expr_kind::Type);
    SET_ENUM("Value",    expr_kind::Value);
    SET_ENUM("Pair",     expr_kind::Pair);
    SET_ENUM("Proj",     expr_kind::Proj);
    SET_ENUM("App",      expr_kind::App);
    SET_ENUM("Sigma",    expr_kind::Sigma);
    SET_ENUM("Lambda",   expr_kind::Lambda);
    SET_ENUM("Pi",       expr_kind::Pi);
    SET_ENUM("Let",      expr_kind::Let);
    SET_ENUM("HEq",      expr_kind::HEq);
    SET_ENUM("MetaVar",  expr_kind::MetaVar);
    lua_setglobal(L, "expr_kind");
}

DECL_UDATA(context_entry)

static int mk_context_entry(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_context_entry(L, context_entry(to_name_ext(L, 1), to_expr(L, 2)));
    else
        return push_context_entry(L, context_entry(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
}

static int context_entry_get_name(lua_State * L) { return push_name(L, to_context_entry(L, 1).get_name()); }
static int context_entry_get_domain(lua_State * L) { return push_optional_expr(L, to_context_entry(L, 1).get_domain()); }
static int context_entry_get_body(lua_State * L) { return push_optional_expr(L, to_context_entry(L, 1).get_body()); }

static const struct luaL_Reg context_entry_m[] = {
    {"__gc",            context_entry_gc}, // never throws
    {"get_name",        safe_function<context_entry_get_name>},
    {"get_domain",      safe_function<context_entry_get_domain>},
    {"get_body",        safe_function<context_entry_get_body>},
    {0, 0}
};

DECL_UDATA(context)

static int context_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(fmt(to_context(L, 1), opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int mk_context(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_context(L, context());
    } else if (nargs == 2) {
        context_entry & e = to_context_entry(L, 2);
        return push_context(L, context(to_context(L, 1), e));
    } else if (nargs == 3) {
        return push_context(L, context(to_context(L, 1), to_name_ext(L, 2), to_expr(L, 3)));
    } else {
        if (lua_isnil(L, 3))
            return push_context(L, context(to_context(L, 1), to_name_ext(L, 2), none_expr(), to_expr(L, 4)));
        else
            return push_context(L, context(to_context(L, 1), to_name_ext(L, 2), to_expr(L, 3), to_expr(L, 4)));
    }
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

static void context_entry_migrate(lua_State * src, int i, lua_State * tgt) {
    push_context_entry(tgt, to_context_entry(src, i));
}

static void context_migrate(lua_State * src, int i, lua_State * tgt) {
    push_context(tgt, to_context(src, i));
}

static void open_context(lua_State * L) {
    luaL_newmetatable(L, context_entry_mt);
    set_migrate_fn_field(L, -1, context_entry_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, context_entry_m, 0);
    SET_GLOBAL_FUN(mk_context_entry,   "context_entry");
    SET_GLOBAL_FUN(context_entry_pred, "is_context_entry");

    luaL_newmetatable(L, context_mt);
    set_migrate_fn_field(L, -1, context_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, context_m, 0);
    SET_GLOBAL_FUN(mk_context,     "context");
    SET_GLOBAL_FUN(context_pred,   "is_context");
    SET_GLOBAL_FUN(context_extend, "extend");
    SET_GLOBAL_FUN(context_lookup, "lookup");
}

DECL_UDATA(formatter)

[[ noreturn ]] void throw_invalid_formatter_call() {
    throw exception("invalid formatter invocation, the acceptable arguments are: (expr, options?), (context, options?), (context, expr, bool? options?), (kernel object, options?), (environment, options?)");
}

static int formatter_call_core(lua_State * L) {
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
            ro_shared_environment env(L, 2);
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

static int formatter_call(lua_State * L) {
    formatter & fmt = to_formatter(L, 1);
    optional<ro_environment> env = fmt.get_environment();
    if (env) {
        read_only_shared_environment ro_env(*env);
        return formatter_call_core(L);
    } else {
        return formatter_call_core(L);
    }
}

static const struct luaL_Reg formatter_m[] = {
    {"__gc",            formatter_gc}, // never throws
    {"__call",          safe_function<formatter_call>},
    {0, 0}
};

static char g_formatter_key;
static formatter g_simple_formatter = mk_simple_formatter();

optional<formatter> get_global_formatter_core(lua_State * L) {
    io_state * io = get_io_state(L);
    if (io != nullptr) {
        return optional<formatter>(io->get_formatter());
    } else {
        lua_pushlightuserdata(L, static_cast<void *>(&g_formatter_key));
        lua_gettable(L, LUA_REGISTRYINDEX);
        if (is_formatter(L, -1)) {
            formatter r = to_formatter(L, -1);
            lua_pop(L, 1);
            return optional<formatter>(r);
        } else {
            lua_pop(L, 1);
            return optional<formatter>();
        }
    }
}

formatter get_global_formatter(lua_State * L) {
    auto r = get_global_formatter_core(L);
    if (r)
        return *r;
    else
        return g_simple_formatter;
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

static int get_formatter(lua_State * L) {
    io_state * io = get_io_state(L);
    if (io != nullptr) {
        return push_formatter(L, io->get_formatter());
    } else {
        return push_formatter(L, get_global_formatter(L));
    }
}

static int set_formatter(lua_State * L) {
    set_global_formatter(L, to_formatter(L, 1));
    return 0;
}

static void open_formatter(lua_State * L) {
    luaL_newmetatable(L, formatter_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, formatter_m, 0);

    SET_GLOBAL_FUN(formatter_pred, "is_formatter");
    SET_GLOBAL_FUN(get_formatter,  "get_formatter");
    SET_GLOBAL_FUN(set_formatter,  "set_formatter");
}

DECL_UDATA(environment)
int push_environment(lua_State * L, ro_environment const & env) {
    // Hack to avoid having environment and ro_environment in the Lua API
    // push_environment is a friend of the environment
    return push_environment(L, env.cast_to_environment());
}

static environment get_global_environment(lua_State * L);

ro_shared_environment::ro_shared_environment(lua_State * L, int idx):
    read_only_shared_environment(to_environment(L, idx)) {
}

ro_shared_environment::ro_shared_environment(lua_State * L):
    read_only_shared_environment(get_global_environment(L)) {
}

rw_shared_environment::rw_shared_environment(lua_State * L, int idx):
    read_write_shared_environment(to_environment(L, idx)) {
}

rw_shared_environment::rw_shared_environment(lua_State * L):
    read_write_shared_environment(get_global_environment(L)) {
}

static int mk_empty_environment(lua_State * L) {
    return push_environment(L, environment());
}

static int environment_mk_child(lua_State * L) {
    rw_shared_environment env(L, 1);
    return push_environment(L, env->mk_child());
}

static int environment_has_parent(lua_State * L) {
    ro_shared_environment env(L, 1);
    lua_pushboolean(L, env->has_parent());
    return 1;
}

static int environment_has_children(lua_State * L) {
    ro_shared_environment env(L, 1);
    lua_pushboolean(L, env->has_children());
    return 1;
}

static int environment_parent(lua_State * L) {
    ro_shared_environment env(L, 1);
    if (!env->has_parent())
        throw exception("environment does not have a parent environment");
    return push_environment(L, env->parent());
}

static int environment_add_uvar_cnstr(lua_State * L) {
    rw_shared_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 2)
        env->add_uvar_cnstr(to_name_ext(L, 2));
    else
        env->add_uvar_cnstr(to_name_ext(L, 2), to_level(L, 3));
    return 0;
}

static int environment_is_ge(lua_State * L) {
    ro_shared_environment env(L, 1);
    lua_pushboolean(L, env->is_ge(to_level(L, 2), to_level(L, 3)));
    return 1;
}

static int environment_get_uvar(lua_State * L) {
    ro_shared_environment env(L, 1);
    return push_level(L, env->get_uvar(to_name_ext(L, 2)));
}

static int environment_add_definition(lua_State * L) {
    rw_shared_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 3) {
        env->add_definition(to_name_ext(L, 2), to_expr(L, 3));
    } else if (nargs == 4) {
        if (is_expr(L, 4))
            env->add_definition(to_name_ext(L, 2), to_expr(L, 3), to_expr(L, 4));
        else
            env->add_definition(to_name_ext(L, 2), to_expr(L, 3), lua_toboolean(L, 4));
    } else {
        env->add_definition(to_name_ext(L, 2), to_expr(L, 3), to_expr(L, 4), lua_toboolean(L, 5));
    }
    return 0;
}

static int environment_add_theorem(lua_State * L) {
    rw_shared_environment env(L, 1);
    env->add_theorem(to_name_ext(L, 2), to_expr(L, 3), to_expr(L, 4));
    return 0;
}

static int environment_add_var(lua_State * L) {
    rw_shared_environment env(L, 1);
    env->add_var(to_name_ext(L, 2), to_expr(L, 3));
    return 0;
}

static int environment_add_axiom(lua_State * L) {
    rw_shared_environment env(L, 1);
    env->add_axiom(to_name_ext(L, 2), to_expr(L, 3));
    return 0;
}

static int environment_find_object(lua_State * L) {
    ro_shared_environment env(L, 1);
    return push_optional_object(L, env->find_object(to_name_ext(L, 2)));
}

static int environment_has_object(lua_State * L) {
    ro_shared_environment env(L, 1);
    lua_pushboolean(L, env->has_object(to_name_ext(L, 2)));
    return 1;
}

static int environment_type_check(lua_State * L) {
    ro_shared_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, env->type_check(to_expr(L, 2)));
    else
        return push_expr(L, env->type_check(to_expr(L, 2), to_context(L, 3)));
}

static int environment_normalize(lua_State * L) {
    ro_shared_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, env->normalize(to_expr(L, 2)));
    else
        return push_expr(L, env->normalize(to_expr(L, 2), to_context(L, 3)));
}

/**
   \brief Iterator (closure base function) for kernel objects.

   \see environment_objects
   \see environment_local_objects.
*/
static int environment_next_object(lua_State * L) {
    ro_shared_environment env(L, lua_upvalueindex(1));
    unsigned i   = lua_tointeger(L, lua_upvalueindex(2));
    unsigned num = lua_tointeger(L, lua_upvalueindex(3));
    if (i >= num) {
        lua_pushnil(L);
    } else {
        bool local   = lua_toboolean(L, lua_upvalueindex(4));
        lua_pushinteger(L, i + 1);
        lua_replace(L, lua_upvalueindex(2)); // update closure
        push_object(L, env->get_object(i, local));
    }
    return 1;
}

static int environment_objects_core(lua_State * L, bool local) {
    ro_shared_environment env(L, 1);
    push_environment(L, env);   // upvalue(1): environment
    lua_pushinteger(L, 0);      // upvalue(2): index
    lua_pushinteger(L, env->get_num_objects(local)); // upvalue(3): size
    lua_pushboolean(L, local);  // upvalue(4): local flag
    lua_pushcclosure(L, &safe_function<environment_next_object>, 4); // create closure with 4 upvalues
    return 1;
}

static int environment_objects(lua_State * L) {
    return environment_objects_core(L, false);
}

static int environment_local_objects(lua_State * L) {
    return environment_objects_core(L, true);
}

static int environment_infer_type(lua_State * L) {
    int nargs = lua_gettop(L);
    ro_shared_environment env(L, 1);
    if (nargs == 2)
        return push_expr(L, env->infer_type(to_expr(L, 2)));
    else
        return push_expr(L, env->infer_type(to_expr(L, 2), to_context(L, 3)));
}

static int environment_is_proposition(lua_State * L) {
    int nargs = lua_gettop(L);
    ro_shared_environment env(L, 1);
    if (nargs == 2)
        lua_pushboolean(L, env->is_proposition(to_expr(L, 2)));
    else
        lua_pushboolean(L, env->is_proposition(to_expr(L, 2), to_context(L, 3)));
    return 1;
}

static int environment_tostring(lua_State * L) {
    ro_shared_environment env(L, 1);
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(fmt(env, opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int environment_set_opaque(lua_State * L) {
    rw_shared_environment env(L, 1);
    env->set_opaque(to_name_ext(L, 2), lua_toboolean(L, 3));
    return 0;
}

static int environment_is_opaque(lua_State * L) {
    ro_shared_environment env(L, 1);
    auto obj = env->find_object(to_name_ext(L, 2));
    lua_pushboolean(L, obj && obj->is_opaque());
    return 1;
}

template<typename F>
static int environment_import_core(lua_State * L, F && import) {
    rw_shared_environment env(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 3) {
        import(env, luaL_checkstring(L, 2), to_io_state(L, 3));
    } else {
        io_state * ios = get_io_state(L);
        if (ios) {
            import(env, luaL_checkstring(L, 2), *ios);
        } else {
            io_state ios(mk_simple_formatter());
            ios.set_options(get_global_options(L));
            import(env, luaL_checkstring(L, 2), ios);
        }
    }
    return 0;
}

static int environment_import(lua_State * L) {
    return environment_import_core(L, [](rw_shared_environment & env, char const * fname, io_state const & ios) {
            return env->import(fname, ios);
        });
}

static int environment_load(lua_State * L) {
    return environment_import_core(L, [](rw_shared_environment & env, char const * fname, io_state const & ios) {
            return env->load(fname, ios);
        });
}

static int environment_get_universe_distance(lua_State * L) {
    ro_shared_environment env(L, 1);
    auto r = env->get_universe_distance(to_name_ext(L, 2), to_name_ext(L, 3));
    if (r)
        lua_pushinteger(L, *r);
    else
        lua_pushnil(L);
    return 1;
}

static int environment_imported(lua_State * L) {
    ro_shared_environment env(L, 1);
    lua_pushboolean(L, env->imported(std::string(luaL_checkstring(L, 2))));
    return 1;
}

static const struct luaL_Reg environment_m[] = {
    {"__gc",           environment_gc}, // never throws
    {"__tostring",     safe_function<environment_tostring>},
    {"mk_child",       safe_function<environment_mk_child>},
    {"has_parent",     safe_function<environment_has_parent>},
    {"has_children",   safe_function<environment_has_children>},
    {"parent",         safe_function<environment_parent>},
    {"add_uvar_cnstr", safe_function<environment_add_uvar_cnstr>},
    {"get_universe_distance", safe_function<environment_get_universe_distance>},
    {"is_ge",          safe_function<environment_is_ge>},
    {"get_uvar",       safe_function<environment_get_uvar>},
    {"add_definition", safe_function<environment_add_definition>},
    {"add_theorem",    safe_function<environment_add_theorem>},
    {"add_var",        safe_function<environment_add_var>},
    {"add_axiom",      safe_function<environment_add_axiom>},
    {"find_object",    safe_function<environment_find_object>},
    {"has_object",     safe_function<environment_has_object>},
    {"type_check",     safe_function<environment_type_check>},
    {"infer_type",     safe_function<environment_infer_type>},
    {"normalize",      safe_function<environment_normalize>},
    {"is_proposition", safe_function<environment_is_proposition>},
    {"objects",        safe_function<environment_objects>},
    {"local_objects",  safe_function<environment_local_objects>},
    {"set_opaque",     safe_function<environment_set_opaque>},
    {"is_opaque",      safe_function<environment_is_opaque>},
    {"import",         safe_function<environment_import>},
    {"imported",       safe_function<environment_imported>},
    {"load",           safe_function<environment_load>},
    {0, 0}
};

static char g_set_environment_key;

void set_global_environment(lua_State * L, environment const & env) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_environment_key));
    push_environment(L, env);
    lua_settable(L, LUA_REGISTRYINDEX);
}

set_environment::set_environment(lua_State * L, environment const & env) {
    m_state = L;
    set_global_environment(L, env);
}

set_environment::~set_environment() {
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_environment_key));
    lua_pushnil(m_state);
    lua_settable(m_state, LUA_REGISTRYINDEX);
}

static environment get_global_environment(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_environment_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!is_environment(L, -1))
        throw exception("Lua registry does not contain a Lean environment");
    environment r = to_environment(L, -1);
    lua_pop(L, 1);
    return r;
}

int get_environment(lua_State * L) {
    return push_environment(L, get_global_environment(L));
}

static void environment_migrate(lua_State * src, int i, lua_State * tgt) {
    push_environment(tgt, to_environment(src, i));
}

static void open_environment(lua_State * L) {
    luaL_newmetatable(L, environment_mt);
    set_migrate_fn_field(L, -1, environment_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, environment_m, 0);

    SET_GLOBAL_FUN(mk_empty_environment,   "empty_environment");
    SET_GLOBAL_FUN(environment_pred,       "is_environment");
    SET_GLOBAL_FUN(get_environment,        "get_environment");
    SET_GLOBAL_FUN(get_environment,        "get_env");
}

DECL_UDATA(object)

int push_optional_object(lua_State * L, optional<object> const & o) {
    if (o)
        push_object(L, *o);
    else
        lua_pushnil(L);
    return 1;
}

static int object_keyword(lua_State * L) {
    lua_pushstring(L, to_object(L, 1).keyword());
    return 1;
}

static int object_has_name(lua_State * L) {
    lua_pushboolean(L, to_object(L, 1).has_name());
    return 1;
}

static int object_get_name(lua_State * L) {
    object const & o = to_object(L, 1);
    if (!o.has_name())
        throw exception("kernel object does not have a name");
    return push_name(L, o.get_name());
}

static int object_has_type(lua_State * L) {
    lua_pushboolean(L, to_object(L, 1).has_type());
    return 1;
}

static int object_get_type(lua_State * L) {
    object const & o = to_object(L, 1);
    if (!o.has_type())
        throw exception("kernel object does not have a type");
    return push_expr(L, o.get_type());
}

static int object_has_cnstr_level(lua_State * L) {
    lua_pushboolean(L, to_object(L, 1).has_cnstr_level());
    return 1;
}

static int object_get_cnstr_level(lua_State * L) {
    object const & o = to_object(L, 1);
    if (!o.has_cnstr_level())
        throw exception("kernel object does not have a constraint level");
    return push_level(L, o.get_cnstr_level());
}

static int object_get_value(lua_State * L) {
    object const & o = to_object(L, 1);
    if (!o.is_definition() && !o.is_builtin())
        throw exception("kernel object is not a definition/theorem/builtin");
    return push_expr(L, o.get_value());
}

static int object_get_weight(lua_State * L) {
    object const & o = to_object(L, 1);
    if (!o.is_definition())
        throw exception("kernel object is not a definition");
    lua_pushinteger(L, o.get_weight());
    return 1;
}

#define OBJECT_PRED(P)                                  \
static int object_ ## P(lua_State * L) {                \
    lua_pushboolean(L, to_object(L, 1).P());    \
    return 1;                                           \
}

OBJECT_PRED(is_definition)
OBJECT_PRED(is_opaque)
OBJECT_PRED(is_axiom)
OBJECT_PRED(is_theorem)
OBJECT_PRED(is_var_decl)
OBJECT_PRED(is_builtin)
OBJECT_PRED(is_builtin_set)

#define OBJECT_EXTRA_PRED(P)                    \
static int object_ ## P(lua_State * L) {        \
    lua_pushboolean(L, P(to_object(L, 1)));     \
    return 1;                                   \
}

OBJECT_EXTRA_PRED(is_begin_import)
OBJECT_EXTRA_PRED(is_begin_builtin_import)
OBJECT_EXTRA_PRED(is_end_import)

static int object_in_builtin_set(lua_State * L) {
    lua_pushboolean(L, to_object(L, 1).in_builtin_set(to_expr(L, 2)));
    return 1;
}

static int object_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(fmt(to_object(L, 1), opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static const struct luaL_Reg object_m[] = {
    {"__gc",            object_gc}, // never throws
    {"__tostring",      safe_function<object_tostring>},
    {"keyword",         safe_function<object_keyword>},
    {"has_name",        safe_function<object_has_name>},
    {"get_name",        safe_function<object_get_name>},
    {"has_type",        safe_function<object_has_type>},
    {"get_type",        safe_function<object_get_type>},
    {"has_cnstr_level", safe_function<object_has_cnstr_level>},
    {"get_cnstr_level", safe_function<object_get_cnstr_level>},
    {"is_definition",   safe_function<object_is_definition>},
    {"is_opaque",       safe_function<object_is_opaque>},
    {"get_value",       safe_function<object_get_value>},
    {"get_weight",      safe_function<object_get_weight>},
    {"is_axiom",        safe_function<object_is_axiom>},
    {"is_theorem",      safe_function<object_is_theorem>},
    {"is_var_decl",     safe_function<object_is_var_decl>},
    {"is_builtin",      safe_function<object_is_builtin>},
    {"is_builtin_set",  safe_function<object_is_builtin_set>},
    {"in_builtin_set",  safe_function<object_in_builtin_set>},
    {"is_begin_import", safe_function<object_is_begin_import>},
    {"is_begin_builtin_import", safe_function<object_is_begin_builtin_import>},
    {"is_end_import",   safe_function<object_is_end_import>},
    {0, 0}
};

static void open_object(lua_State * L) {
    luaL_newmetatable(L, object_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, object_m, 0);

    SET_GLOBAL_FUN(object_pred, "is_kernel_object");
}

DECL_UDATA(justification)

int push_optional_justification(lua_State * L, optional<justification> const & j) {
    if (j)
        push_justification(L, *j);
    else
        lua_pushnil(L);
    return 1;
}

static int justification_tostring(lua_State * L) {
    std::ostringstream out;
    justification & jst = to_justification(L, 1);
    if (jst) {
        formatter fmt  = get_global_formatter(L);
        options   opts = get_global_options(L);
        out << mk_pair(jst.pp(fmt, opts), opts);
    } else {
        out << "<null-justification>";
    }
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int justification_has_children(lua_State * L) {
    lua_pushboolean(L, to_justification(L, 1).has_children());
    return 1;
}

static int justification_is_null(lua_State * L) {
    lua_pushboolean(L, !to_justification(L, 1));
    return 1;
}

/**
   \brief Iterator (closure base function) for justification children. See \c justification_children
*/
static int justification_next_child(lua_State * L) {
    unsigned i    = lua_tointeger(L, lua_upvalueindex(2));
    unsigned num  = objlen(L, lua_upvalueindex(1));
    if (i > num) {
        lua_pushnil(L);
    } else {
        lua_pushinteger(L, i + 1);
        lua_replace(L, lua_upvalueindex(2)); // update i
        lua_rawgeti(L, lua_upvalueindex(1), i); // read children[i]
    }
    return 1;
}

static int justification_children(lua_State * L) {
    buffer<justification_cell*> children;
    to_justification(L, 1).get_children(children);
    lua_newtable(L);
    int i = 1;
    for (auto jcell : children) {
        push_justification(L, justification(jcell));
        lua_rawseti(L, -2, i);
        i = i + 1;
    }
    lua_pushinteger(L, 1);
    lua_pushcclosure(L, &safe_function<justification_next_child>, 2); // create closure with 2 upvalues
    return 1;
}

static int justification_get_main_expr(lua_State * L) {
    optional<expr> r = to_justification(L, 1).get_main_expr();
    if (r)
        push_expr(L, *r);
    else
        lua_pushnil(L);
    return 1;
}

static int justification_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    justification & jst = to_justification(L, 1);
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    bool display_children = true;

    if (nargs == 2) {
        if (lua_isboolean(L, 2)) {
            display_children = lua_toboolean(L, 2);
        } else {
            luaL_checktype(L, 2, LUA_TTABLE);

            lua_pushstring(L, "formatter");
            lua_gettable(L, 2);
            if (is_formatter(L, -1))
                fmt = to_formatter(L, -1);
            lua_pop(L, 1);

            lua_pushstring(L, "options");
            lua_gettable(L, 2);
            if (is_options(L, -1))
                opts = to_options(L, -1);
            lua_pop(L, 1);

            lua_pushstring(L, "display_children");
            lua_gettable(L, 2);
            if (lua_isboolean(L, -1))
                display_children = lua_toboolean(L, -1);
            lua_pop(L, 1);
        }
    }
    return push_format(L, jst.pp(fmt, opts, nullptr, display_children));
}

static int justification_depends_on(lua_State * L) {
    lua_pushboolean(L, depends_on(to_justification(L, 1), to_justification(L, 2)));
    return 1;
}

static int mk_assumption_justification(lua_State * L) {
    return push_justification(L, mk_assumption_justification(luaL_checkinteger(L, 1)));
}

static const struct luaL_Reg justification_m[] = {
    {"__gc",            justification_gc}, // never throws
    {"__tostring",      safe_function<justification_tostring>},
    {"is_null",         safe_function<justification_is_null>},
    {"has_children",    safe_function<justification_has_children>},
    {"children",        safe_function<justification_children>},
    {"get_main_expr",   safe_function<justification_get_main_expr>},
    {"pp",              safe_function<justification_pp>},
    {"depends_on",      safe_function<justification_depends_on>},
    {0, 0}
};

static void open_justification(lua_State * L) {
    luaL_newmetatable(L, justification_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, justification_m, 0);

    SET_GLOBAL_FUN(mk_assumption_justification, "mk_assumption_justification");
    SET_GLOBAL_FUN(justification_pred, "is_justification");
}

DECL_UDATA(metavar_env)

static int menv_mk_metavar(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1) {
        return push_expr(L, to_metavar_env(L, 1)->mk_metavar());
    } else if (nargs == 2) {
        return push_expr(L, to_metavar_env(L, 1)->mk_metavar(to_context(L, 2)));
    } else {
        return push_expr(L, to_metavar_env(L, 1)->mk_metavar(to_context(L, 2), some_expr(to_expr(L, 3))));
    }
}

static expr & to_metavar(lua_State * L, int i, bool lctx = true) {
    expr & e = to_expr(L, i);
    if (is_metavar(e)) {
        if (lctx || !has_local_context(e))
            return e;
        throw exception(sstream() << "arg #" << i << " must be a metavariable without a local context");
    }
    throw exception(sstream() << "arg #" << i << " must be a metavariable");
}

static int menv_get_timestamp(lua_State * L) {
    lua_pushinteger(L, to_metavar_env(L, 1)->get_timestamp());
    return 1;
}

static int menv_get_context(lua_State * L) {
    if (is_expr(L, 2))
        return push_context(L, to_metavar_env(L, 1)->get_context(to_metavar(L, 2, false)));
    else
        return push_context(L, to_metavar_env(L, 1)->get_context(to_name_ext(L, 2)));
}

static int menv_has_type(lua_State * L) {
    if (is_expr(L, 2))
        lua_pushboolean(L, to_metavar_env(L, 1)->has_type(to_metavar(L, 2)));
    else
        lua_pushboolean(L, to_metavar_env(L, 1)->has_type(to_name_ext(L, 2)));
    return 1;
}

static int menv_get_type(lua_State * L) {
    if (is_expr(L, 2))
        return push_expr(L, to_metavar_env(L, 1)->get_type(to_metavar(L, 2)));
    else
        return push_expr(L, to_metavar_env(L, 1)->get_type(to_name_ext(L, 2)));
}

static int menv_is_assigned(lua_State * L) {
    if (is_expr(L, 2))
        lua_pushboolean(L, to_metavar_env(L, 1)->is_assigned(to_metavar(L, 2)));
    else
        lua_pushboolean(L, to_metavar_env(L, 1)->is_assigned(to_name_ext(L, 2)));
    return 1;
}

static int menv_assign(lua_State * L) {
    int nargs = lua_gettop(L);
    justification jst;
    if (nargs == 4)
        jst = to_justification(L, 4);
    if (is_expr(L, 2))
        to_metavar_env(L, 1)->assign(to_metavar(L, 2, false), to_expr(L, 3), jst);
    else
        to_metavar_env(L, 1)->assign(to_name_ext(L, 2), to_expr(L, 3), jst);
    return 0;
}

static int menv_get_subst(lua_State * L) {
    if (is_expr(L, 2))
        return push_optional_expr(L, to_metavar_env(L, 1)->get_subst(to_metavar(L, 2)));
    else
        return push_optional_expr(L, to_metavar_env(L, 1)->get_subst(to_name_ext(L, 2)));
}

static int menv_get_justification(lua_State * L) {
    if (is_expr(L, 2))
        return push_optional_justification(L, to_metavar_env(L, 1)->get_justification(to_metavar(L, 2)));
    else
        return push_optional_justification(L, to_metavar_env(L, 1)->get_justification(to_name_ext(L, 2)));
}

static int menv_get_subst_jst(lua_State * L) {
    optional<std::pair<expr, justification>> r;
    if (is_expr(L, 2)) {
        r = to_metavar_env(L, 1)->get_subst_jst(to_metavar(L, 2));
    } else {
        r = to_metavar_env(L, 1)->get_subst_jst(to_name_ext(L, 2));
    }
    if (r) {
        push_expr(L, r->first);
        push_justification(L, r->second);
        return 2;
    } else {
        return 0;
    }
}

static int menv_for_each_subst(lua_State * L) {
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    to_metavar_env(L, 1)->for_each_subst([&](name const & n, expr const & e) {
            lua_pushvalue(L, 2); // push user-fun
            push_name(L, n);
            push_expr(L, e);
            pcall(L, 2, 0, 0);
        });
    return 0;
}

static int mk_metavar_env(lua_State * L) {
    if (lua_gettop(L) == 1)
        return push_metavar_env(L, metavar_env(to_name_ext(L, 1)));
    else
        return push_metavar_env(L, metavar_env());
}

static int menv_copy(lua_State * L) {
    return push_metavar_env(L, metavar_env(to_metavar_env(L, 1).copy()));
}

static int instantiate_metavars(lua_State * L) {
    return push_expr(L, to_metavar_env(L, 2)->instantiate_metavars(to_expr(L, 1)));
}

static const struct luaL_Reg metavar_env_m[] = {
    {"__gc",              metavar_env_gc}, // never throws
    {"mk_metavar",        safe_function<menv_mk_metavar>},
    {"get_timestamp",     safe_function<menv_get_timestamp>},
    {"get_context",       safe_function<menv_get_context>},
    {"has_type",          safe_function<menv_has_type>},
    {"get_type",          safe_function<menv_get_type>},
    {"is_assigned",       safe_function<menv_is_assigned>},
    {"assign",            safe_function<menv_assign>},
    {"get_subst",         safe_function<menv_get_subst>},
    {"get_justification", safe_function<menv_get_justification>},
    {"get_subst_jst",     safe_function<menv_get_subst_jst>},
    {"for_each_subst",    safe_function<menv_for_each_subst>},
    {"copy",              safe_function<menv_copy>},
    {0, 0}
};

static void open_metavar_env(lua_State * L) {
    luaL_newmetatable(L, metavar_env_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, metavar_env_m, 0);

    SET_GLOBAL_FUN(mk_metavar_env,   "metavar_env");
    SET_GLOBAL_FUN(metavar_env_pred, "is_metavar_env");
    SET_GLOBAL_FUN(instantiate_metavars, "instantiate_metavars");
}

constexpr char const * type_inferer_mt = "type_inferer";
type_inferer & to_type_inferer(lua_State * L, int i) { return *static_cast<type_inferer*>(luaL_checkudata(L, i, type_inferer_mt)); }
DECL_PRED(type_inferer)
DECL_GC(type_inferer)

static int type_inferer_call(lua_State * L) {
    int nargs = lua_gettop(L);
    type_inferer & inferer = to_type_inferer(L, 1);
    if (nargs == 2)
        return push_expr(L, inferer(to_expr(L, 2)));
    else
        return push_expr(L, inferer(to_expr(L, 2), to_context(L, 3)));
}

static int type_inferer_clear(lua_State * L) {
    to_type_inferer(L, 1).clear();
    return 0;
}

static int mk_type_inferer(lua_State * L) {
    void * mem = lua_newuserdata(L, sizeof(type_inferer));
    new (mem) type_inferer(to_environment(L, 1));
    luaL_getmetatable(L, type_inferer_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static const struct luaL_Reg type_inferer_m[] = {
    {"__gc",            type_inferer_gc}, // never throws
    {"__call",          safe_function<type_inferer_call>},
    {"clear",           safe_function<type_inferer_clear>},
    {0, 0}
};

void open_type_inferer(lua_State * L) {
    luaL_newmetatable(L, type_inferer_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, type_inferer_m, 0);

    SET_GLOBAL_FUN(mk_type_inferer,          "type_inferer");
    SET_GLOBAL_FUN(type_inferer_pred,        "is_type_inferer");
}

DECL_UDATA(io_state)

int mk_io_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_io_state(L, io_state(mk_simple_formatter()));
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

static mutex g_print_mutex;

static void print(io_state * ios, bool reg, char const * msg) {
    if (ios) {
        if (reg)
            regular(*ios) << msg;
        else
            diagnostic(*ios) << msg;
    } else {
        std::cout << msg;
    }
}

/** \brief Thread safe version of print function */
static int print(lua_State * L, int start, bool reg) {
    lock_guard<mutex> lock(g_print_mutex);
    io_state * ios = get_io_state(L);
    int n = lua_gettop(L);
    int i;
    lua_getglobal(L, "tostring");
    for (i = start; i <= n; i++) {
        char const * s;
        size_t l;
        lua_pushvalue(L, -1);
        lua_pushvalue(L, i);
        lua_call(L, 1, 1);
        s = lua_tolstring(L, -1, &l);
        if (s == NULL)
            throw exception("'to_string' must return a string to 'print'");
        if (i > start) {
            print(ios, reg, "\t");
        }
        print(ios, reg, s);
        lua_pop(L, 1);
    }
    print(ios, reg, "\n");
    return 0;
}

static int print(lua_State * L, io_state & ios, int start, bool reg) {
    set_io_state set(L, ios);
    return print(L, start, reg);
}

static int print(lua_State * L) {
    return print(L, 1, true);
}

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
    SET_GLOBAL_FUN(print, "print");
}

static char g_set_state_key;

void set_global_io_state(lua_State * L, io_state & ios) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(L, &ios);
    lua_settable(L, LUA_REGISTRYINDEX);
    set_global_options(L, ios.get_options());
}

set_io_state::set_io_state(lua_State * L, io_state & st) {
    m_state = L;
    m_prev  = get_io_state(L);
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(m_state, &st);
    lua_settable(m_state, LUA_REGISTRYINDEX);
    if (!m_prev)
        m_prev_options = get_global_options(m_state);
    set_global_options(m_state, st.get_options());
}

set_io_state::~set_io_state() {
    lua_pushlightuserdata(m_state, static_cast<void *>(&g_set_state_key));
    lua_pushlightuserdata(m_state, m_prev);
    lua_settable(m_state, LUA_REGISTRYINDEX);
    if (!m_prev)
        set_global_options(m_state, m_prev_options);
    else
        set_global_options(m_state, m_prev->get_options());
}

io_state * get_io_state(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_state_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (lua_islightuserdata(L, -1)) {
        io_state * r = static_cast<io_state*>(lua_touserdata(L, -1));
        if (r) {
            lua_pop(L, 1);
            options o = get_global_options(L);
            r->set_options(o);
            return r;
        }
    }
    lua_pop(L, 1);
    return nullptr;
}

void open_kernel_module(lua_State * L) {
    open_level(L);
    open_local_context(L);
    open_expr(L);
    open_context(L);
    open_formatter(L);
    open_environment(L);
    open_object(L);
    open_justification(L);
    open_metavar_env(L);
    open_type_inferer(L);
    open_io_state(L);
}
}
#endif
