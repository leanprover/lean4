/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/sstream.h"
#include "util/script_state.h"
#include "util/lua_list.h"
#include "util/lua_pair.h"
#include "util/lua_named_param.h"
#include "util/lazy_list_fn.h"
#include "util/luaref.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/metavar.h"
#include "kernel/error_msgs.h"
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/standard_kernel.h"
#include "library/occurs.h"
#include "library/io_state_stream.h"
#include "library/expr_lt.h"
#include "library/kernel_bindings.h"
#include "library/normalize.h"
#include "library/module.h"
#include "library/reducible.h"
#include "library/print.h"
#include "library/unfold_macros.h"

// Lua Bindings for the Kernel classes. We do not include the Lua
// bindings in the kernel because we do not want to inflate the Kernel.

// In Lua, we can use the notations
//   - l + k for succ^k(l)
//   - k     for succ^k(zero)
// The following definition is a limit on the k's that are considered.
#ifndef LEAN_MAX_LEVEL_OFFSET_IN_LUA
#define LEAN_MAX_LEVEL_OFFSET_IN_LUA 1024
#endif

namespace lean {
environment get_global_environment(lua_State * L);
io_state * get_io_state_ptr(lua_State * L);
io_state get_tmp_io_state(lua_State * L);
io_state get_io_state(lua_State * L) {
    if (io_state * ios = get_io_state_ptr(L))
        return *ios;
    else
        return get_tmp_io_state(L);
}

// Level
DECL_UDATA(level)

int push_optional_level(lua_State * L, optional<level> const & l) {  return l ? push_level(L, *l) : push_nil(L); }

static level mk_offset(level const & l, int k) {
    if (k < 0) throw exception(sstream() << "invalid level offset " << k << ", offsets must be nonnegative");
    else if (k > LEAN_MAX_LEVEL_OFFSET_IN_LUA) throw exception(sstream() << "invalid level offset " << k << ", offset is too big");
    level r = l;
    while (k > 0) {
        k--;
        r = mk_succ(r);
    }
    return r;
}

static level to_level_ext(lua_State * L, int idx) {
    if (lua_isnumber(L, idx))
        return mk_offset(mk_level_zero(), lua_tonumber(L, idx));
    else if (lua_isstring(L, idx) || is_name(L, idx))
        return mk_param_univ(to_name_ext(L, idx));
    else
        return to_level(L, idx);
}

DEFINE_LUA_LIST(level, push_level, to_level_ext)

static int level_add(lua_State * L) {
    return push_level(L, mk_offset(to_level(L, 1), luaL_checkinteger(L, 2)));
}

static int level_tostring(lua_State * L) {
    std::ostringstream out;
    options opts  = get_global_options(L);
    out << mk_pair(pp(to_level(L, 1), opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int level_eq(lua_State * L) { return push_boolean(L, to_level(L, 1) == to_level(L, 2)); }
static int level_lt(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_boolean(L, is_lt(to_level(L, 1), to_level(L, 2), nargs == 3 && lua_toboolean(L, 3)));
}
static int mk_level_zero(lua_State * L)  { return push_level(L, mk_level_zero()); }
static int mk_level_one(lua_State * L)   { return push_level(L, mk_level_one());  }
static int mk_level_succ(lua_State * L)  { return push_level(L, mk_succ(to_level_ext(L, 1))); }
template<level (*F)(level const & l1, level const & l2)>
static int mk_level_max_core(lua_State * L)   {
    int nargs = lua_gettop(L);
    level r;
    if (nargs == 0) {
        r = mk_level_zero();
    } else if (nargs == 1) {
        r = to_level_ext(L, 1);
    } else {
        r = F(to_level_ext(L, nargs - 1), to_level_ext(L, nargs));
        for (int i = nargs - 2; i >= 1; i--)
            r = F(to_level_ext(L, i), r);
    }
    return push_level(L, r);
}
static int mk_level_max(lua_State * L) { return mk_level_max_core<mk_max>(L); }
static int mk_level_imax(lua_State * L) { return mk_level_max_core<mk_imax>(L); }
static int mk_param_univ(lua_State * L)  { return push_level(L, mk_param_univ(to_name_ext(L, 1))); }
static int mk_global_univ(lua_State * L) { return push_level(L, mk_global_univ(to_name_ext(L, 1))); }
static int mk_meta_univ(lua_State * L)   { return push_level(L, mk_meta_univ(to_name_ext(L, 1))); }
#define LEVEL_PRED(P) static int level_ ## P(lua_State * L) { check_num_args(L, 1); return push_boolean(L, P(to_level(L, 1))); }
LEVEL_PRED(is_zero)
LEVEL_PRED(is_param)
LEVEL_PRED(is_global)
LEVEL_PRED(is_meta)
LEVEL_PRED(is_succ)
LEVEL_PRED(is_max)
LEVEL_PRED(is_imax)
LEVEL_PRED(is_explicit)
LEVEL_PRED(has_meta)
LEVEL_PRED(has_param)
LEVEL_PRED(is_not_zero)
static int level_normalize(lua_State * L)  { return push_level(L, normalize(to_level(L, 1))); }
static int level_get_kind(lua_State * L) { return push_integer(L, static_cast<int>(kind(to_level(L, 1)))); }
static int level_is_equivalent(lua_State * L) { return push_boolean(L, is_equivalent(to_level(L, 1), to_level_ext(L, 2))); }
static int level_is_eqp(lua_State * L) { return push_boolean(L, is_eqp(to_level(L, 1), to_level(L, 2))); }

static int level_id(lua_State * L) {
    level const & l = to_level(L, 1);
    if (is_param(l))       return push_name(L, param_id(l));
    else if (is_global(l)) return push_name(L, global_id(l));
    else if (is_meta(l))   return push_name(L, meta_id(l));
    else throw exception("arg #1 must be a level parameter/global/metavariable");
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

static int level_instantiate(lua_State * L) {
    auto ps = to_list_name_ext(L, 2);
    auto ls = to_list_level_ext(L, 3);
    if (length(ps) != length(ls))
        throw exception("arg #2 and #3 size do not match");
    return push_level(L, instantiate(to_level(L, 1), ps, ls));
}

static int level_is_geq_core(lua_State * L) { return push_boolean(L, is_geq_core(to_level(L, 1), to_level_ext(L, 2))); }
static int level_is_geq(lua_State * L) { return push_boolean(L, is_geq(to_level(L, 1), to_level_ext(L, 2))); }

static const struct luaL_Reg level_m[] = {
    {"__gc",            level_gc}, // never throws
    {"__tostring",      safe_function<level_tostring>},
    {"__eq",            safe_function<level_eq>},
    {"__lt",            safe_function<level_lt>},
    {"__add",           safe_function<level_add>},
    {"succ",            safe_function<mk_level_succ>},
    {"kind",            safe_function<level_get_kind>},
    {"is_zero",         safe_function<level_is_zero>},
    {"is_param",        safe_function<level_is_param>},
    {"is_global",       safe_function<level_is_global>},
    {"is_meta",         safe_function<level_is_meta>},
    {"is_succ",         safe_function<level_is_succ>},
    {"is_max",          safe_function<level_is_max>},
    {"is_imax",         safe_function<level_is_imax>},
    {"is_explicit",     safe_function<level_is_explicit>},
    {"has_meta",        safe_function<level_has_meta>},
    {"has_param",       safe_function<level_has_param>},
    {"is_not_zero",     safe_function<level_is_not_zero>},
    {"is_equivalent",   safe_function<level_is_equivalent>},
    {"is_eqp",          safe_function<level_is_eqp>},
    {"is_lt",           safe_function<level_lt>},
    {"is_geq",          safe_function<level_is_geq>},
    {"is_geq_core",     safe_function<level_is_geq_core>},
    {"id",              safe_function<level_id>},
    {"lhs",             safe_function<level_lhs>},
    {"rhs",             safe_function<level_rhs>},
    {"succ_of",         safe_function<level_succ_of>},
    {"instantiate",     safe_function<level_instantiate>},
    {"normalize",       safe_function<level_normalize>},
    {"norm",            safe_function<level_normalize>},
    {0, 0}
};

static void open_level(lua_State * L) {
    luaL_newmetatable(L, level_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, level_m, 0);

    SET_GLOBAL_FUN(mk_level_zero,   "level");
    SET_GLOBAL_FUN(mk_level_zero,   "mk_level_zero");
    SET_GLOBAL_FUN(mk_level_one,    "mk_level_one");
    SET_GLOBAL_FUN(mk_level_succ,   "mk_level_succ");
    SET_GLOBAL_FUN(mk_level_max,    "mk_level_max");
    SET_GLOBAL_FUN(mk_level_imax,   "mk_level_imax");
    SET_GLOBAL_FUN(mk_param_univ,   "mk_param_univ");
    SET_GLOBAL_FUN(mk_global_univ,  "mk_global_univ");
    SET_GLOBAL_FUN(mk_meta_univ,    "mk_meta_univ");
    SET_GLOBAL_FUN(mk_level_succ,   "succ_univ");
    SET_GLOBAL_FUN(mk_level_max,    "max_univ");
    SET_GLOBAL_FUN(mk_level_imax,   "imax_univ");
    SET_GLOBAL_FUN(mk_param_univ,   "param_univ");
    SET_GLOBAL_FUN(mk_global_univ,  "global_univ");
    SET_GLOBAL_FUN(mk_meta_univ,    "meta_univ");

    SET_GLOBAL_FUN(level_pred, "is_level");

    lua_newtable(L);
    SET_ENUM("Zero",      level_kind::Zero);
    SET_ENUM("Succ",      level_kind::Succ);
    SET_ENUM("Max",       level_kind::Max);
    SET_ENUM("IMax",      level_kind::IMax);
    SET_ENUM("Global",    level_kind::Global);
    SET_ENUM("Param",     level_kind::Param);
    SET_ENUM("Meta",      level_kind::Meta);
    lua_setglobal(L, "level_kind");
}

static list<name> to_level_param_names(lua_State * L, int _idx) {
    if (is_list_name(L, _idx)) {
        return to_list_name(L, _idx);
    } else{
        return table_to_list<name>(L, _idx, [=](lua_State * L, int idx) -> name {
                if (is_level(L, idx)) {
                    level const & l = to_level(L, idx);
                    if (is_param(l))
                        return param_id(l);
                    else if (is_global(l))
                        return global_id(l);
                    else
                        throw exception(sstream() << "arg #" << _idx << " contain a level expression that is not a parameter/global");
                } else {
                    return to_name_ext(L, idx);
                }
            });
    }
}

// Expr_binder_info
DECL_UDATA(binder_info)
static int mk_binder_info(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_binder_info(L, binder_info());
    else if (nargs == 1)
        return push_binder_info(L, binder_info(lua_toboolean(L, 1)));
    else if (nargs == 2)
        return push_binder_info(L, binder_info(lua_toboolean(L, 1), lua_toboolean(L, 2)));
    else if (nargs == 3)
        return push_binder_info(L, binder_info(lua_toboolean(L, 1), lua_toboolean(L, 2), lua_toboolean(L, 3)));
    else
        return push_binder_info(L, binder_info(lua_toboolean(L, 1), lua_toboolean(L, 2), lua_toboolean(L, 3), lua_toboolean(L, 4)));
}
static int binder_info_is_implicit(lua_State * L) { return push_boolean(L, to_binder_info(L, 1).is_implicit()); }
static int binder_info_is_cast(lua_State * L) { return push_boolean(L, to_binder_info(L, 1).is_cast()); }
static int binder_info_is_contextual(lua_State * L) { return push_boolean(L, to_binder_info(L, 1).is_contextual()); }
static int binder_info_is_strict_implicit(lua_State * L) { return push_boolean(L, to_binder_info(L, 1).is_strict_implicit()); }
static int binder_info_is_inst_implicit(lua_State * L) { return push_boolean(L, to_binder_info(L, 1).is_inst_implicit()); }
static const struct luaL_Reg binder_info_m[] = {
    {"__gc",               binder_info_gc},
    {"is_implicit",        safe_function<binder_info_is_implicit>},
    {"is_cast",            safe_function<binder_info_is_cast>},
    {"is_contextual",      safe_function<binder_info_is_contextual>},
    {"is_strict_implicit", safe_function<binder_info_is_strict_implicit>},
    {"is_inst_implicit",   safe_function<binder_info_is_inst_implicit>},
    {0, 0}
};
static void open_binder_info(lua_State * L) {
    luaL_newmetatable(L, binder_info_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, binder_info_m, 0);

    SET_GLOBAL_FUN(mk_binder_info, "binder_info");
    SET_GLOBAL_FUN(binder_info_pred, "is_binder_info");
}

// Expressions
DECL_UDATA(expr)
DEFINE_LUA_LIST(expr, push_expr, to_expr)

int push_optional_expr(lua_State * L, optional<expr> const & e) {  return e ? push_expr(L, *e) : push_nil(L); }

expr & to_app(lua_State * L, int idx) {
    expr & r = to_expr(L, idx);
    if (!is_app(r))
        throw exception(sstream() << "arg #" << idx << " must be an application");
    return r;
}

expr & to_binding(lua_State * L, int idx) {
    expr & r = to_expr(L, idx);
    if (!is_binding(r))
        throw exception(sstream() << "arg #" << idx << " must be a binder (i.e., lambda or Pi)");
    return r;
}

expr & to_macro_app(lua_State * L, int idx) {
    expr & r = to_expr(L, idx);
    if (!is_macro(r))
        throw exception(sstream() << "arg #" << idx << " must be a macro application");
    return r;
}

static int expr_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt   = mk_formatter(L);
    options   opts  = get_global_options(L);
    out << mk_pair(fmt(to_expr(L, 1)), opts);
    return push_string(L, out.str().c_str());
}

static int expr_is_equal(lua_State * L) { return push_boolean(L, to_expr(L, 1) == to_expr(L, 2)); }
static int expr_is_bi_equal(lua_State * L) { return push_boolean(L, is_bi_equal(to_expr(L, 1), to_expr(L, 2))); }
static int expr_lt(lua_State * L) { return push_boolean(L, to_expr(L, 1) < to_expr(L, 2)); }
static int expr_mk_constant(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_expr(L, mk_constant(to_name_ext(L, 1)));
    else
        return push_expr(L, mk_constant(to_name_ext(L, 1), to_list_level_ext(L, 2)));
}
static int expr_mk_var(lua_State * L) { return push_expr(L, mk_var(luaL_checkinteger(L, 1))); }
static int expr_mk_app(lua_State * L) {
    int nargs = lua_gettop(L);
    expr r;
    r = mk_app(to_expr(L, 1), to_expr(L, 2));
    for (int i = 3; i <= nargs; i++)
        r = mk_app(r, to_expr(L, i));
    return push_expr(L, r);
}
static int expr_mk_lambda(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3)
        return push_expr(L, mk_lambda(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
    else
        return push_expr(L, mk_lambda(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3), to_binder_info(L, 4)));
}
static int expr_mk_pi(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3)
        return push_expr(L, mk_pi(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3)));
    else
        return push_expr(L, mk_pi(to_name_ext(L, 1), to_expr(L, 2), to_expr(L, 3), to_binder_info(L, 4)));
}
static int expr_mk_arrow(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs < 2)
        throw exception("function must have at least 2 arguments");
    expr r = mk_arrow(to_expr(L, nargs - 1), to_expr(L, nargs));
    for (int i = nargs - 2; i >= 1; i--)
        r = mk_arrow(to_expr(L, i), r);
    return push_expr(L, r);
}

typedef expr (*MkAbst1)(expr const & n, expr const & t, expr const & b);
typedef expr (*MkAbst2)(name const & n, expr const & t, expr const & b);

template<bool pi>
static int expr_abst(lua_State * L) {
    int nargs = lua_gettop(L);
    check_atleast_num_args(L, 2);
    expr r = to_expr(L, nargs);
    for (int i = nargs - 1; i >= 1; i -= 1) {
        expr l = to_expr(L, i);
        if (!is_local(l))
            throw exception(sstream() << "arg #" << i << " must be a local constants");
        if (pi)
            r = Pi(l, r);
        else
            r = Fun(l, r);
    }
    return push_expr(L, r);
}

static int expr_fun(lua_State * L) { return expr_abst<false>(L); }
static int expr_pi(lua_State * L)  { return expr_abst<true>(L); }
static int expr_mk_sort(lua_State * L) { return push_expr(L, mk_sort(to_level_ext(L, 1))); }
static int expr_mk_metavar(lua_State * L) { return push_expr(L, mk_metavar(to_name_ext(L, 1), to_expr(L, 2))); }
static int expr_mk_local(lua_State * L) {
    int nargs = lua_gettop(L);
    name n    = to_name_ext(L, 1);
    if (nargs == 2)
        return push_expr(L, mk_local(n, to_expr(L, 2)));
    else if (nargs == 3 && is_binder_info(L, 3))
        return push_expr(L, mk_local(n, n, to_expr(L, 2), to_binder_info(L, 3)));
    else if (nargs == 3)
        return push_expr(L, mk_local(n, to_name_ext(L, 2), to_expr(L, 3), binder_info()));
    else
        return push_expr(L, mk_local(n, to_name_ext(L, 2), to_expr(L, 3), to_binder_info(L, 4)));
}
static int expr_get_kind(lua_State * L) { return push_integer(L, static_cast<int>(to_expr(L, 1).kind())); }

#define EXPR_PRED(P) static int expr_ ## P(lua_State * L) { check_num_args(L, 1); return push_boolean(L, P(to_expr(L, 1))); }

EXPR_PRED(is_constant)
EXPR_PRED(is_var)
EXPR_PRED(is_app)
EXPR_PRED(is_lambda)
EXPR_PRED(is_pi)
EXPR_PRED(is_binding)
EXPR_PRED(is_macro)
EXPR_PRED(is_metavar)
EXPR_PRED(is_local)
EXPR_PRED(is_mlocal)
EXPR_PRED(is_meta)
EXPR_PRED(has_metavar)
EXPR_PRED(has_local)
EXPR_PRED(has_param_univ)
EXPR_PRED(has_free_vars)
EXPR_PRED(closed)

static int expr_fields(lua_State * L) {
    expr & e = to_expr(L, 1);
    switch (e.kind()) {
    case expr_kind::Var:
        return push_integer(L, var_idx(e));
    case expr_kind::Constant:
        push_name(L, const_name(e)); push_list_level(L, const_levels(e)); return 2;
    case expr_kind::Sort:
        return push_level(L, sort_level(e));
    case expr_kind::Macro:
        return push_macro_definition(L, macro_def(e));
    case expr_kind::App:
        push_expr(L, app_fn(e)); push_expr(L, app_arg(e)); return 2;
    case expr_kind::Lambda:
    case expr_kind::Pi:
        push_name(L, binding_name(e)); push_expr(L, binding_domain(e)); push_expr(L, binding_body(e)); push_binder_info(L, binding_info(e)); return 4;
    case expr_kind::Meta:
    case expr_kind::Local:
        push_name(L, mlocal_name(e)); push_expr(L, mlocal_type(e)); return 2;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
    return 0;           // LCOV_EXCL_LINE
}

static int expr_fn(lua_State * L) { return push_expr(L, app_fn(to_app(L, 1))); }
static int expr_arg(lua_State * L) { return push_expr(L, app_arg(to_app(L, 1))); }

static int expr_for_each(lua_State * L) {
    expr const & e = to_expr(L, 1);    // expr
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    for_each(e, [&](expr const & a, unsigned offset) {
            lua_pushvalue(L, 2); // push user-fun
            push_expr(L, a);
            lua_pushinteger(L, offset);
            pcall(L, 2, 1, 0);
            bool r = true;
            if (lua_isboolean(L, -1))
                r = lua_toboolean(L, -1);
            lua_pop(L, 1);
            return r;
        });
    return 0;
}

static int expr_replace(lua_State * L) {
    expr const & e = to_expr(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION);
    expr r = replace(e, [&](expr const & a, unsigned offset) {
            lua_pushvalue(L, 2);
            push_expr(L, a);
            lua_pushinteger(L, offset);
            pcall(L, 2, 1, 0);
            if (is_expr(L, -1)) {
                expr r = to_expr(L, -1);
                lua_pop(L, 1);
                return some_expr(r);
            } else {
                lua_pop(L, 1);
                return none_expr();
            }
        });
    return push_expr(L, r);
}

static int expr_has_free_var(lua_State * L) {
    return push_boolean(L, has_free_var(to_expr(L, 1), luaL_checkinteger(L, 2)));
}

static int expr_lift_free_vars(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_expr(L, lift_free_vars(to_expr(L, 1), luaL_checkinteger(L, 2)));
    else
        return push_expr(L, lift_free_vars(to_expr(L, 1), luaL_checkinteger(L, 2), luaL_checkinteger(L, 3)));
}

static int expr_lower_free_vars(lua_State * L) {
    check_atmost_num_args(L, 3);
    int nargs = lua_gettop(L);
    expr const & e = to_expr(L, 1);
    int s          = luaL_checkinteger(L, 2);
    if (nargs == 2) {
        return push_expr(L, lower_free_vars(e, s));
    } else {
        int d = luaL_checkinteger(L, 3);
        if (s < d)
            throw exception(sstream() << "invalid lower_free_vars, first argument must be >= second one");
        return push_expr(L, lower_free_vars(e, s, d));
    }
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

static int expr_instantiate_univ_params(lua_State * L) {
    return push_expr(L, instantiate_univ_params(to_expr(L, 1), to_level_param_names(L, 2), to_list_level_ext(L, 3)));
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

static int binding_name(lua_State * L) { return push_name(L, binding_name(to_binding(L, 1))); }
static int binding_domain(lua_State * L) { return push_expr(L, binding_domain(to_binding(L, 1))); }
static int binding_body(lua_State * L) { return push_expr(L, binding_body(to_binding(L, 1))); }
static int binding_info(lua_State * L) { return push_binder_info(L, binding_info(to_binding(L, 1))); }

static int expr_occurs(lua_State * L)  { return push_boolean(L, occurs(to_expr(L, 1), to_expr(L, 2))); }
static int expr_is_eqp(lua_State * L)  { return push_boolean(L, is_eqp(to_expr(L, 1), to_expr(L, 2))); }
static int expr_hash(lua_State * L)    { return push_integer(L, to_expr(L, 1).hash()); }
static int expr_hash_bi(lua_State * L) { return push_integer(L, hash_bi(to_expr(L, 1))); }
static int expr_weight(lua_State * L)  { return push_integer(L, get_weight(to_expr(L, 1))); }
static int expr_is_lt(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_boolean(L, is_lt(to_expr(L, 1), to_expr(L, 2), nargs == 3 && lua_toboolean(L, 3)));
}
static int expr_mk_macro(lua_State * L) {
    buffer<expr> args;
    copy_lua_array(L, 2, args);
    return push_expr(L, mk_macro(to_macro_definition(L, 1), args.size(), args.data()));
}

static int macro_def(lua_State * L) { return push_macro_definition(L, macro_def(to_macro_app(L, 1))); }
static int macro_num_args(lua_State * L) { return push_integer(L, macro_num_args(to_macro_app(L, 1))); }
static int macro_arg(lua_State * L) { return push_expr(L, macro_arg(to_macro_app(L, 1), luaL_checkinteger(L, 2))); }

static int expr_set_tag(lua_State * L) { to_expr(L, 1).set_tag(luaL_checkinteger(L, 2)); return 0; }
static int expr_tag(lua_State * L) {
    auto t = to_expr(L, 1).get_tag();
    return (t == nulltag) ? push_nil(L) : push_integer(L, t);
}

static const struct luaL_Reg expr_m[] = {
    {"__gc",             expr_gc}, // never throws
    {"__tostring",       safe_function<expr_tostring>},
    {"__eq",             safe_function<expr_is_equal>},
    {"__lt",             safe_function<expr_lt>},
    {"__call",           safe_function<expr_mk_app>},
    {"kind",             safe_function<expr_get_kind>},
    {"is_var",           safe_function<expr_is_var>},
    {"is_constant",      safe_function<expr_is_constant>},
    {"is_metavar",       safe_function<expr_is_metavar>},
    {"is_local",         safe_function<expr_is_local>},
    {"is_mlocal",        safe_function<expr_is_mlocal>},
    {"is_app",           safe_function<expr_is_app>},
    {"is_lambda",        safe_function<expr_is_lambda>},
    {"is_pi",            safe_function<expr_is_pi>},
    {"is_binding",       safe_function<expr_is_binding>},
    {"is_macro",         safe_function<expr_is_macro>},
    {"is_meta",          safe_function<expr_is_meta>},
    {"has_free_vars",    safe_function<expr_has_free_vars>},
    {"closed",           safe_function<expr_closed>},
    {"has_metavar",      safe_function<expr_has_metavar>},
    {"has_local",        safe_function<expr_has_local>},
    {"has_param_univ",   safe_function<expr_has_param_univ>},
    {"arg",              safe_function<expr_arg>},
    {"fn",               safe_function<expr_fn>},
    {"fields",           safe_function<expr_fields>},
    {"data",             safe_function<expr_fields>},
    {"weight",           safe_function<expr_weight>},
    {"binding_name",     safe_function<binding_name>},
    {"binding_domain",   safe_function<binding_domain>},
    {"binding_body",     safe_function<binding_body>},
    {"binding_info",     safe_function<binding_info>},
    {"macro_def",        safe_function<macro_def>},
    {"macro_num_args",   safe_function<macro_num_args>},
    {"macro_arg",        safe_function<macro_arg>},
    {"for_each",         safe_function<expr_for_each>},
    {"replace",          safe_function<expr_replace>},
    {"has_free_var",     safe_function<expr_has_free_var>},
    {"lift_free_vars",   safe_function<expr_lift_free_vars>},
    {"lower_free_vars",  safe_function<expr_lower_free_vars>},
    {"instantiate",      safe_function<expr_instantiate>},
    {"instantiate_univs", safe_function<expr_instantiate_univ_params>},
    {"abstract",         safe_function<expr_abstract>},
    {"occurs",           safe_function<expr_occurs>},
    {"is_eqp",           safe_function<expr_is_eqp>},
    {"is_lt",            safe_function<expr_is_lt>},
    {"is_equal",         safe_function<expr_is_equal>},
    {"is_bi_equal",      safe_function<expr_is_bi_equal>},
    {"hash",             safe_function<expr_hash>},
    {"hash_bi",          safe_function<expr_hash_bi>},
    {"tag",              safe_function<expr_tag>},
    {"set_tag",          safe_function<expr_set_tag>},
    {0, 0}
};

static int enable_expr_caching(lua_State * L) { return push_boolean(L, enable_expr_caching(lua_toboolean(L, 1))); }

static void open_expr(lua_State * L) {
    luaL_newmetatable(L, expr_mt);
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
    SET_GLOBAL_FUN(expr_mk_macro,    "mk_macro");
    SET_GLOBAL_FUN(expr_fun,         "fun");
    SET_GLOBAL_FUN(expr_fun,         "Fun");
    SET_GLOBAL_FUN(expr_pi,          "Pi");
    SET_GLOBAL_FUN(expr_mk_sort,     "mk_sort");
    SET_GLOBAL_FUN(expr_mk_metavar,  "mk_metavar");
    SET_GLOBAL_FUN(expr_mk_local,    "mk_local");
    SET_GLOBAL_FUN(expr_mk_local,    "Local");
    SET_GLOBAL_FUN(expr_pred,        "is_expr");

    SET_GLOBAL_FUN(enable_expr_caching, "enable_expr_caching");

    push_expr(L, mk_Prop());
    lua_setglobal(L, "Prop");

    push_expr(L, mk_Type());
    lua_setglobal(L, "Type");

    lua_newtable(L);
    SET_ENUM("Var",      expr_kind::Var);
    SET_ENUM("Constant", expr_kind::Constant);
    SET_ENUM("Meta",     expr_kind::Meta);
    SET_ENUM("Local",    expr_kind::Local);
    SET_ENUM("Sort",     expr_kind::Sort);
    SET_ENUM("App",      expr_kind::App);
    SET_ENUM("Lambda",   expr_kind::Lambda);
    SET_ENUM("Pi",       expr_kind::Pi);
    SET_ENUM("Macro",    expr_kind::Macro);
    lua_setglobal(L, "expr_kind");
}
// macro_definition
DECL_UDATA(macro_definition)
static int macro_get_name(lua_State * L) { return push_name(L, to_macro_definition(L, 1).get_name()); }
static int macro_trust_level(lua_State * L) { return push_integer(L, to_macro_definition(L, 1).trust_level()); }
static int macro_eq(lua_State * L) { return push_boolean(L, to_macro_definition(L, 1) == to_macro_definition(L, 2)); }
static int macro_hash(lua_State * L) { return push_integer(L, to_macro_definition(L, 1).hash()); }
static int macro_tostring(lua_State * L) {
    std::ostringstream out;
    formatter fmt   = mk_formatter(L);
    options opts    = get_global_options(L);
    out << mk_pair(to_macro_definition(L, 1).pp(fmt), opts);
    return push_string(L, out.str().c_str());
}

static const struct luaL_Reg macro_definition_m[] = {
    {"__gc",             macro_definition_gc}, // never throws
    {"__tostring",       safe_function<macro_tostring>},
    {"__eq",             safe_function<macro_eq>},
    {"hash",             safe_function<macro_hash>},
    {"trust_level",      safe_function<macro_trust_level>},
    {"name",             safe_function<macro_get_name>},
    {0, 0}
};

static void open_macro_definition(lua_State * L) {
    luaL_newmetatable(L, macro_definition_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, macro_definition_m, 0);

    SET_GLOBAL_FUN(macro_definition_pred, "is_macro_definition");
}

// declaration
DECL_UDATA(declaration)
int push_optional_declaration(lua_State * L, optional<declaration> const & e) {  return e ? push_declaration(L, *e) : push_nil(L); }
#define DECLARATION_PRED(P) static int declaration_ ## P(lua_State * L) { check_num_args(L, 1); return push_boolean(L, to_declaration(L, 1).P()); }
DECLARATION_PRED(is_definition)
DECLARATION_PRED(is_theorem)
DECLARATION_PRED(is_axiom)
DECLARATION_PRED(is_constant_assumption)
DECLARATION_PRED(use_conv_opt)
static int declaration_get_name(lua_State * L) { return push_name(L, to_declaration(L, 1).get_name()); }
static int declaration_get_params(lua_State * L) { return push_list_name(L, to_declaration(L, 1).get_univ_params()); }
static int declaration_get_type(lua_State * L) { return push_expr(L, to_declaration(L, 1).get_type()); }
static int declaration_get_value(lua_State * L) {
    if (to_declaration(L, 1).is_definition())
        return push_expr(L, to_declaration(L, 1).get_value());
    throw exception("arg #1 must be a definition");
}
static int declaration_get_weight(lua_State * L) { return push_integer(L, to_declaration(L, 1).get_weight()); }
static int mk_constant_assumption(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_declaration(L, mk_constant_assumption(to_name_ext(L, 1), level_param_names(), to_expr(L, 2)));
    else
        return push_declaration(L, mk_constant_assumption(to_name_ext(L, 1), to_level_param_names(L, 2), to_expr(L, 3)));
}
static int mk_axiom(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_declaration(L, mk_axiom(to_name_ext(L, 1), level_param_names(), to_expr(L, 2)));
    else
        return push_declaration(L, mk_axiom(to_name_ext(L, 1), to_level_param_names(L, 2), to_expr(L, 3)));
}
static void get_definition_args(lua_State * L, int idx, unsigned & weight, bool & use_conv_opt) {
    use_conv_opt = get_bool_named_param(L, idx, "use_conv_opt", use_conv_opt);
    weight       = get_uint_named_param(L, idx, "weight", weight);
}
static int mk_definition(lua_State * L) {
    int nargs = lua_gettop(L);
    unsigned weight = 0; bool use_conv_opt = true;
    if (nargs < 3) {
        throw exception("mk_definition must have at least 3 arguments");
    } else if (is_environment(L, 1)) {
        if (nargs < 4) {
            throw exception("mk_definition must have at least 4 arguments, when the first argument is an environment");
        } else if (is_expr(L, 3)) {
            get_definition_args(L, 5, weight, use_conv_opt);
            return push_declaration(L, mk_definition(to_environment(L, 1), to_name_ext(L, 2), level_param_names(),
                                                    to_expr(L, 3), to_expr(L, 4), use_conv_opt));
        } else {
            get_definition_args(L, 6, weight, use_conv_opt);
            return push_declaration(L, mk_definition(to_environment(L, 1), to_name_ext(L, 2), to_level_param_names(L, 3),
                                                    to_expr(L, 4), to_expr(L, 5), use_conv_opt));
        }
    } else {
        if (is_expr(L, 2)) {
            get_definition_args(L, 4, weight, use_conv_opt);
            return push_declaration(L, mk_definition(to_name_ext(L, 1), level_param_names(), to_expr(L, 2),
                                                    to_expr(L, 3), weight, use_conv_opt));
        } else {
            get_definition_args(L, 5, weight, use_conv_opt);
            return push_declaration(L, mk_definition(to_name_ext(L, 1), to_level_param_names(L, 2),
                                                    to_expr(L, 3), to_expr(L, 4), weight, use_conv_opt));
        }
    }
}
static void get_definition_args(lua_State * L, int idx, unsigned & weight) {
    weight       = get_uint_named_param(L, idx, "weight", weight);
}
static int mk_theorem(lua_State * L) {
    int nargs = lua_gettop(L);
    unsigned weight = 0;
    if (nargs == 3) {
          return push_declaration(L, mk_theorem(to_name_ext(L, 1), level_param_names(), to_expr(L, 2), to_expr(L, 3), 0));
    } else if (nargs == 4) {
        if (is_expr(L, 4)) {
            return push_declaration(L, mk_theorem(to_name_ext(L, 1), to_level_param_names(L, 2), to_expr(L, 3), to_expr(L, 4),
                                                  weight));
        } else {
            get_definition_args(L, 4, weight);
            return push_declaration(L, mk_theorem(to_name_ext(L, 1), level_param_names(), to_expr(L, 2), to_expr(L, 3), weight));
        }
    } else {
        get_definition_args(L, 5, weight);
        return push_declaration(L, mk_theorem(to_name_ext(L, 1), to_level_param_names(L, 2), to_expr(L, 3), to_expr(L, 4), weight));
    }
}

static const struct luaL_Reg declaration_m[] = {
    {"__gc",             declaration_gc}, // never throws
    {"is_definition",    safe_function<declaration_is_definition>},
    {"is_theorem",       safe_function<declaration_is_theorem>},
    {"is_axiom",         safe_function<declaration_is_axiom>},
    {"is_constant_assumption", safe_function<declaration_is_constant_assumption>},
    {"use_conv_opt",     safe_function<declaration_use_conv_opt>},
    {"name",             safe_function<declaration_get_name>},
    {"univ_params",      safe_function<declaration_get_params>},
    {"type",             safe_function<declaration_get_type>},
    {"value",            safe_function<declaration_get_value>},
    {"weight",           safe_function<declaration_get_weight>},
    {0, 0}
};

static void open_declaration(lua_State * L) {
    luaL_newmetatable(L, declaration_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, declaration_m, 0);

    SET_GLOBAL_FUN(declaration_pred,       "is_declaration");
    SET_GLOBAL_FUN(mk_constant_assumption, "mk_constant_assumption");
    SET_GLOBAL_FUN(mk_axiom,               "mk_axiom");
    SET_GLOBAL_FUN(mk_theorem,             "mk_theorem");
    SET_GLOBAL_FUN(mk_definition,          "mk_definition");
}

// Formatter
DECL_UDATA(formatter_factory)
DECL_UDATA(formatter)

static int formatter_call(lua_State * L) {
    formatter & fmt = to_formatter(L, 1);
    return push_format(L, fmt(to_expr(L, 2)));
}

static int formatter_factory_call(lua_State * L) {
    int nargs = lua_gettop(L);
    formatter_factory & fmtf = to_formatter_factory(L, 1);
    if (nargs == 1)
        return push_formatter(L, fmtf(get_global_environment(L), get_global_options(L)));
    else if (nargs == 2)
        return push_formatter(L, fmtf(to_environment(L, 2), get_global_options(L)));
    else
        return push_formatter(L, fmtf(to_environment(L, 2), to_options(L, 3)));
}

static const struct luaL_Reg formatter_factory_m[] = {
    {"__gc",            formatter_factory_gc}, // never throws
    {"__call",          safe_function<formatter_factory_call>},
    {0, 0}
};

static const struct luaL_Reg formatter_m[] = {
    {"__gc",            formatter_gc}, // never throws
    {"__call",          safe_function<formatter_call>},
    {0, 0}
};

static char g_formatter_factory_key;
static formatter_factory * g_print_formatter_factory = nullptr;

optional<formatter_factory> get_global_formatter_factory_core(lua_State * L) {
    io_state * io = get_io_state_ptr(L);
    if (io != nullptr) {
        return optional<formatter_factory>(io->get_formatter_factory());
    } else {
        lua_pushlightuserdata(L, static_cast<void *>(&g_formatter_factory_key));
        lua_gettable(L, LUA_REGISTRYINDEX);
        if (is_formatter_factory(L, -1)) {
            formatter_factory r = to_formatter_factory(L, -1);
            lua_pop(L, 1);
            return optional<formatter_factory>(r);
        } else {
            lua_pop(L, 1);
            return optional<formatter_factory>();
        }
    }
}

formatter_factory get_global_formatter_factory(lua_State * L) {
    auto r = get_global_formatter_factory_core(L);
    if (r)
        return *r;
    else
        return *g_print_formatter_factory;
}

void set_global_formatter_factory(lua_State * L, formatter_factory const & fmtf) {
    io_state * io = get_io_state_ptr(L);
    if (io != nullptr) {
        io->set_formatter_factory(fmtf);
    } else {
        lua_pushlightuserdata(L, static_cast<void *>(&g_formatter_factory_key));
        push_formatter_factory(L, fmtf);
        lua_settable(L, LUA_REGISTRYINDEX);
    }
}

static int get_formatter_factory(lua_State * L) {
    io_state * io = get_io_state_ptr(L);
    if (io != nullptr) {
        return push_formatter_factory(L, io->get_formatter_factory());
    } else {
        return push_formatter_factory(L, get_global_formatter_factory(L));
    }
}

formatter mk_formatter(lua_State * L) {
    return get_global_formatter_factory(L)(get_global_environment(L), get_global_options(L));
}

static int set_formatter_factory(lua_State * L) {
    set_global_formatter_factory(L, to_formatter_factory(L, 1));
    return 0;
}

static void open_formatter(lua_State * L) {
    luaL_newmetatable(L, formatter_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, formatter_m, 0);

    luaL_newmetatable(L, formatter_factory_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, formatter_factory_m, 0);

    SET_GLOBAL_FUN(formatter_pred, "is_formatter");
    SET_GLOBAL_FUN(formatter_factory_pred, "is_formatter_factory");
    SET_GLOBAL_FUN(get_formatter_factory,  "get_formatter_factory");
    SET_GLOBAL_FUN(set_formatter_factory,  "set_formatter_factory");
}

// Helper function for push pair expr, constraint_seq
int push_ecs(lua_State * L, pair<expr, constraint_seq> const & p) {
    push_expr(L, p.first);
    push_constraint_seq(L, p.second);
    return 2;
}

int push_bcs(lua_State * L, pair<bool, constraint_seq> const & p) {
    push_boolean(L, p.first);
    push_constraint_seq(L, p.second);
    return 2;
}

// Environment_id
DECL_UDATA(environment_id)
static int environment_id_descendant(lua_State * L) { return push_boolean(L, to_environment_id(L, 1).is_descendant(to_environment_id(L, 2))); }
static const struct luaL_Reg environment_id_m[] = {
    {"__gc",             environment_id_gc}, // never throws
    {"is_descendant",    safe_function<environment_id_descendant>},
    {0, 0}
};

static void open_environment_id(lua_State * L) {
    luaL_newmetatable(L, environment_id_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, environment_id_m, 0);

    SET_GLOBAL_FUN(environment_id_pred, "is_environment_id");
}

// certified_declaration
DECL_UDATA(certified_declaration)
static int certified_declaration_get_declaration(lua_State * L) { return push_declaration(L, to_certified_declaration(L, 1).get_declaration()); }
static int certified_declaration_get_id(lua_State * L) { return push_environment_id(L, to_certified_declaration(L, 1). get_id()); }

static const struct luaL_Reg certified_declaration_m[] = {
    {"__gc",             certified_declaration_gc}, // never throws
    {"declaration",       safe_function<certified_declaration_get_declaration>},
    {"environment_id",   safe_function<certified_declaration_get_id>},
    {0, 0}
};

static void open_certified_declaration(lua_State * L) {
    luaL_newmetatable(L, certified_declaration_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, certified_declaration_m, 0);

    SET_GLOBAL_FUN(certified_declaration_pred, "is_certified_declaration");
}
static bool operator!=(certified_declaration const &, certified_declaration const &) { return true; }
DEFINE_LUA_LIST(certified_declaration, push_certified_declaration, to_certified_declaration)

// Environment
DECL_UDATA(environment)
static int environment_is_descendant(lua_State * L) { return push_boolean(L, to_environment(L, 1).is_descendant(to_environment(L, 2))); }
static int environment_trust_lvl(lua_State * L) { return push_integer(L, to_environment(L, 1).trust_lvl()); }
static int environment_prop_proof_irrel(lua_State * L) { return push_boolean(L, to_environment(L, 1).prop_proof_irrel()); }
static int environment_eta(lua_State * L) { return push_boolean(L, to_environment(L, 1).eta()); }
static int environment_impredicative(lua_State * L) { return push_boolean(L, to_environment(L, 1).impredicative()); }
static int environment_add_universe(lua_State * L) {
    return push_environment(L, module::add_universe(to_environment(L, 1), to_name_ext(L, 2)));
}
static int environment_is_universe(lua_State * L) { return push_boolean(L, to_environment(L, 1).is_universe(to_name_ext(L, 2))); }
static int environment_find(lua_State * L) { return push_optional_declaration(L, to_environment(L, 1).find(to_name_ext(L, 2))); }
static int environment_get(lua_State * L) { return push_declaration(L, to_environment(L, 1).get(to_name_ext(L, 2))); }
static int environment_add(lua_State * L) {
    if (is_declaration(L, 2))
        return push_environment(L, module::add(to_environment(L, 1), to_declaration(L, 2)));
    else
        return push_environment(L, module::add(to_environment(L, 1), to_certified_declaration(L, 2)));
}
static int environment_replace(lua_State * L) { return push_environment(L, to_environment(L, 1).replace(to_certified_declaration(L, 2))); }
static int mk_bare_environment(lua_State * L) {
    unsigned trust_lvl    = get_uint_named_param(L, 1, "trust_lvl", 0);
    trust_lvl             = get_uint_named_param(L, 1, "trust_level", trust_lvl);
    bool prop_proof_irrel = get_bool_named_param(L, 1, "prop_proof_irrel", true);
    bool eta              = get_bool_named_param(L, 1, "eta", true);
    bool impredicative    = get_bool_named_param(L, 1, "impredicative", true);
    return push_environment(L, environment(trust_lvl, prop_proof_irrel, eta, impredicative));
}
static unsigned get_trust_lvl(lua_State * L, int i) {
    unsigned trust_lvl = 0;
    if (i <= lua_gettop(L))
        trust_lvl = lua_tonumber(L, i);
    return trust_lvl;
}
static int mk_environment(lua_State * L)      { return push_environment(L, mk_environment(get_trust_lvl(L, 1))); }

static int environment_forget(lua_State * L) { return push_environment(L, to_environment(L, 1).forget()); }
static int environment_whnf(lua_State * L) { return push_ecs(L, type_checker(to_environment(L, 1)).whnf(to_expr(L, 2))); }
static int environment_normalize(lua_State * L) { return push_expr(L, normalize(to_environment(L, 1), to_expr(L, 2))); }
static int environment_infer_type(lua_State * L) { return push_ecs(L, type_checker(to_environment(L, 1)).infer(to_expr(L, 2))); }
static int environment_type_check(lua_State * L) { return push_ecs(L, type_checker(to_environment(L, 1)).check(to_expr(L, 2))); }
static int environment_for_each_decl(lua_State * L) {
    environment const & env = to_environment(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    env.for_each_declaration([&](declaration const & d) {
            lua_pushvalue(L, 2); // push user-fun
            push_declaration(L, d);
            pcall(L, 1, 0, 0);
        });
    return 0;
}
static int environment_for_each_universe(lua_State * L) {
    environment const & env = to_environment(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    env.for_each_universe([&](name const & u) {
            lua_pushvalue(L, 2); // push user-fun
            push_name(L, u);
            pcall(L, 1, 0, 0);
        });
    return 0;
}

static void to_module_name_buffer(lua_State * L, int i, buffer<module_name> & r) {
    if (lua_isstring(L, i) || is_name(L, i)) {
        r.push_back(module_name(to_name_ext(L, i)));
    } else {
        luaL_checktype(L, i, LUA_TTABLE);
        lua_pushvalue(L, i);
        int sz = objlen(L, -1);
        for (int i = 1; i <= sz; i++) {
            lua_rawgeti(L, -1, i);
            r.push_back(module_name(to_name_ext(L, -1)));
            lua_pop(L, 1);
        }
    }
}

static int import_modules(environment const & env, lua_State * L, int s) {
    int nargs = lua_gettop(L);
    buffer<module_name> mnames;
    to_module_name_buffer(L, s, mnames);
    unsigned num_threads = 1;
    bool     keep_proofs = false;
    if (nargs > s) {
        num_threads = get_uint_named_param(L, s+1, "num_threads", num_threads);
        keep_proofs = get_bool_named_param(L, s+1, "keep_proofs", keep_proofs);
    }
    std::string base;
    if (nargs > s+1 && is_io_state(L, s+2))
        return push_environment(L, import_modules(env, base, mnames.size(), mnames.data(), num_threads, keep_proofs, to_io_state(L, s+2)));
    else
        return push_environment(L, import_modules(env, base, mnames.size(), mnames.data(), num_threads, keep_proofs, get_io_state(L)));
}

static int import_modules(lua_State * L) {
    if (is_environment(L, 1))
        return import_modules(to_environment(L, 1), L, 2);
    else
        return import_modules(mk_environment(), L, 1);
}

static int export_module(lua_State * L) {
    std::ofstream out(lua_tostring(L, 2), std::ofstream::binary);
    export_module(out, to_environment(L, 1));
    return 0;
}

static const struct luaL_Reg environment_m[] = {
    {"__gc",                  environment_gc}, // never throws
    {"is_descendant",         safe_function<environment_is_descendant>},
    {"trust_lvl",             safe_function<environment_trust_lvl>},
    {"trust_level",           safe_function<environment_trust_lvl>},
    {"prop_proof_irrel",      safe_function<environment_prop_proof_irrel>},
    {"eta",                   safe_function<environment_eta>},
    {"impredicative",         safe_function<environment_impredicative>},
    {"add_universe",          safe_function<environment_add_universe>},
    {"is_universe",           safe_function<environment_is_universe>},
    {"find",                  safe_function<environment_find>},
    {"get",                   safe_function<environment_get>},
    {"add",                   safe_function<environment_add>},
    {"replace",               safe_function<environment_replace>},
    {"forget",                safe_function<environment_forget>},
    {"whnf",                  safe_function<environment_whnf>},
    {"normalize",             safe_function<environment_normalize>},
    {"infer_type",            safe_function<environment_infer_type>},
    {"type_check",            safe_function<environment_type_check>},
    {"for_each_declaration",  safe_function<environment_for_each_decl>},
    {"for_each_decl",         safe_function<environment_for_each_decl>},
    {"for_each_universe",     safe_function<environment_for_each_universe>},
    {"for_each_univ",         safe_function<environment_for_each_universe>},
    {"export",                safe_function<export_module>},
    {0, 0}
};

static char g_set_environment_key;
static environment * get_global_environment_ptr(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_environment_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!lua_islightuserdata(L, -1))
        return nullptr;
    environment * r = static_cast<environment*>(const_cast<void*>(lua_topointer(L, -1)));
    lua_pop(L, 1);
    return r;
}
static void set_global_environment_ptr(lua_State * L, environment * env) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_environment_key));
    lua_pushlightuserdata(L, static_cast<void *>(env));
    lua_settable(L, LUA_REGISTRYINDEX);
}
environment get_global_environment(lua_State * L) {
    environment * env = get_global_environment_ptr(L);
    if (env == nullptr)
        throw exception("Lua state does not have an environment object");
    return *env;
}

set_environment::set_environment(lua_State * L, environment & env):m_state(L) {
    m_old_env = get_global_environment_ptr(L);
    set_global_environment_ptr(L, &env);
}

set_environment::~set_environment() {
    set_global_environment_ptr(m_state, m_old_env);
}

int get_environment(lua_State * L) {
    return push_environment(L, get_global_environment(L));
}

int set_environment(lua_State * L) {
    environment * env = get_global_environment_ptr(L);
    if (env == nullptr)
        throw exception("Lua state does not have an environment object");
    *env = to_environment(L, 1);
    return 0;
}

static void open_environment(lua_State * L) {
    luaL_newmetatable(L, environment_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, environment_m, 0);

    SET_GLOBAL_FUN(mk_bare_environment,    "bare_environment");
    SET_GLOBAL_FUN(mk_environment,         "environment");
    SET_GLOBAL_FUN(environment_pred,       "is_environment");
    SET_GLOBAL_FUN(get_environment,        "get_environment");
    SET_GLOBAL_FUN(get_environment,        "get_env");
    SET_GLOBAL_FUN(set_environment,        "set_environment");
    SET_GLOBAL_FUN(set_environment,        "set_env");
    SET_GLOBAL_FUN(import_modules,         "import_modules");
    SET_GLOBAL_FUN(export_module,          "export_module");
}

// IO state
DECL_UDATA(io_state)

io_state to_io_state_ext(lua_State * L, int idx) {
    if (idx <= lua_gettop(L))
        return to_io_state(L, idx);
    else
        return get_io_state(L);
}

int mk_io_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_io_state(L, io_state(mk_print_formatter_factory()));
    else if (nargs == 1)
        return push_io_state(L, io_state(to_io_state(L, 1)));
    else
        return push_io_state(L, io_state(to_options(L, 1), to_formatter_factory(L, 2)));
}

static int io_state_get_options(lua_State * L) { return push_options(L, to_io_state(L, 1).get_options()); }
static int io_state_get_formatter_factory(lua_State * L) { return push_formatter_factory(L, to_io_state(L, 1).get_formatter_factory()); }
static int io_state_set_options(lua_State * L) { to_io_state(L, 1).set_options(to_options(L, 2)); return 0; }

static mutex * g_print_mutex = nullptr;

static void print(io_state * ios, bool reg, char const * msg) {
    if (ios) {
        if (reg)
            ios->get_regular_channel() << msg;
        else
            ios->get_diagnostic_channel() << msg;
    } else {
        std::cout << msg;
    }
}

/** \brief Thread safe version of print function */
static int print(lua_State * L, int start, bool reg) {
    lock_guard<mutex> lock(*g_print_mutex);
    io_state * ios = get_io_state_ptr(L);
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
            throw exception("'tostring' must return a string to 'print'");
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

static int print(lua_State * L) { return print(L, 1, true); }
static int io_state_print_regular(lua_State * L) { return print(L, to_io_state(L, 1), 2, true); }
static int io_state_print_diagnostic(lua_State * L) { return print(L, to_io_state(L, 1), 2, false); }

static const struct luaL_Reg io_state_m[] = {
    {"__gc",                  io_state_gc}, // never throws
    {"get_options",           safe_function<io_state_get_options>},
    {"set_options",           safe_function<io_state_set_options>},
    {"get_formatter_factory", safe_function<io_state_get_formatter_factory>},
    {"print_diagnostic",      safe_function<io_state_print_diagnostic>},
    {"print_regular",         safe_function<io_state_print_regular>},
    {"print",                 safe_function<io_state_print_regular>},
    {"diagnostic",            safe_function<io_state_print_diagnostic>},
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
    m_prev  = get_io_state_ptr(L);
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

io_state * get_io_state_ptr(lua_State * L) {
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

io_state get_tmp_io_state(lua_State * L) {
    return io_state(get_global_options(L), get_global_formatter_factory(L));
}

// Justification
DECL_UDATA(justification)

int push_optional_justification(lua_State * L, optional<justification> const & j) { return j ? push_justification(L, *j) : push_nil(L); }

static int justification_tostring(lua_State * L) {
    std::ostringstream out;
    justification & jst = to_justification(L, 1);
    out << jst;
    lua_pushstring(L, out.str().c_str());
    return 1;
}

#define JST_PRED(P) static int justification_ ## P(lua_State * L) { check_num_args(L, 1); return push_boolean(L, to_justification(L, 1).P()); }
JST_PRED(is_none)
JST_PRED(is_asserted)
JST_PRED(is_assumption)
JST_PRED(is_composite)
static int justification_get_main_expr(lua_State * L) { return push_optional_expr(L, to_justification(L, 1).get_main_expr()); }
static int justification_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    justification & j = to_justification(L, 1);
    if (nargs == 1)
        return push_format(L, j.pp(mk_formatter(L), nullptr, substitution()));
    else if (nargs == 2 && is_substitution(L, 2))
        return push_format(L, j.pp(mk_formatter(L), nullptr, to_substitution(L, 2)));
    else if (nargs == 2)
        return push_format(L, j.pp(to_formatter(L, 2), nullptr, substitution()));
    else
        return push_format(L, j.pp(to_formatter(L, 2), nullptr, to_substitution(L, 3)));
}
static int justification_assumption_idx(lua_State * L) {
    if (!to_justification(L, 1).is_assumption())
        throw exception("arg #1 must be an assumption justification");
    return push_integer(L, assumption_idx(to_justification(L, 1)));
}
static int justification_child1(lua_State * L) {
    if (!to_justification(L, 1).is_composite())
        throw exception("arg #1 must be a composite justification");
    return push_justification(L, composite_child1(to_justification(L, 1)));
}
static int justification_child2(lua_State * L) {
    if (!to_justification(L, 1).is_composite())
        throw exception("arg #1 must be a composite justification");
    return push_justification(L, composite_child2(to_justification(L, 1)));
}
static int justification_depends_on(lua_State * L) { return push_boolean(L, depends_on(to_justification(L, 1), luaL_checkinteger(L, 2))); }
static int mk_assumption_justification(lua_State * L) { return push_justification(L, mk_assumption_justification(luaL_checkinteger(L, 1))); }
static int mk_composite1(lua_State * L) { return push_justification(L, mk_composite1(to_justification(L, 1), to_justification(L, 2))); }
static int mk_justification(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_justification(L, justification());
    } else if (nargs == 1) {
        std::string s = lua_tostring(L, 1);
        return push_justification(L, mk_justification(none_expr(), [=](formatter const &, substitution const &) {
                    return format(s.c_str());
                }));
    } else {
        std::string s   = lua_tostring(L, 1);
        environment env = to_environment(L, 2);
        expr e          = to_expr(L, 3);
        justification j = mk_justification(some_expr(e), [=](formatter const & fmt, substitution const & subst) {
                expr new_e = substitution(subst).instantiate(e);
                format r;
                r += format(s.c_str());
                r += pp_indent_expr(fmt, new_e);
                return r;
            });
        return push_justification(L, j);
    }
}
static int justification_is_eqp(lua_State * L) { return push_boolean(L, is_eqp(to_justification(L, 1), to_justification(L, 2))); }

static const struct luaL_Reg justification_m[] = {
    {"__gc",            justification_gc}, // never throws
    {"__tostring",      safe_function<justification_tostring>},
    {"is_none",         safe_function<justification_is_none>},
    {"is_asserted",     safe_function<justification_is_asserted>},
    {"is_assumption",   safe_function<justification_is_assumption>},
    {"is_composite",    safe_function<justification_is_composite>},
    {"main_expr",       safe_function<justification_get_main_expr>},
    {"pp",              safe_function<justification_pp>},
    {"depends_on",      safe_function<justification_depends_on>},
    {"assumption_idx",  safe_function<justification_assumption_idx>},
    {"child1",          safe_function<justification_child1>},
    {"child2",          safe_function<justification_child2>},
    {"is_eqp",          safe_function<justification_is_eqp>},
    {0, 0}
};

static void open_justification(lua_State * L) {
    luaL_newmetatable(L, justification_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, justification_m, 0);

    SET_GLOBAL_FUN(mk_justification, "justification");
    SET_GLOBAL_FUN(mk_assumption_justification, "assumption_justification");
    SET_GLOBAL_FUN(mk_composite1, "mk_composite_justification");
    SET_GLOBAL_FUN(justification_pred, "is_justification");
}

// Constraint
DECL_UDATA(constraint)
DEFINE_LUA_LIST(constraint, push_constraint, to_constraint)
int push_optional_constraint(lua_State * L, optional<constraint> const & c) {  return c ? push_constraint(L, *c) : push_nil(L); }
#define CNSTR_PRED(P) static int constraint_ ## P(lua_State * L) { check_num_args(L, 1); return push_boolean(L, P(to_constraint(L, 1))); }
CNSTR_PRED(is_eq_cnstr)
CNSTR_PRED(is_level_eq_cnstr)
CNSTR_PRED(is_choice_cnstr)
static int constraint_is_eqp(lua_State * L) { return push_boolean(L, is_eqp(to_constraint(L, 1), to_constraint(L, 2))); }
static int constraint_get_kind(lua_State * L) { return push_integer(L, static_cast<int>(to_constraint(L, 1).kind())); }
static int constraint_jst(lua_State * L) { return push_justification(L, to_constraint(L, 1).get_justification()); }
static int constraint_lhs(lua_State * L) {
    constraint const & c = to_constraint(L, 1);
    if (is_eq_cnstr(c))
        return push_expr(L, cnstr_lhs_expr(c));
    else if (is_level_eq_cnstr(c))
        return push_level(L, cnstr_lhs_level(c));
    else
        throw exception("arg #1 must be an equality/level constraint");
}
static int constraint_rhs(lua_State * L) {
    constraint const & c = to_constraint(L, 1);
    if (is_eq_cnstr(c))
        return push_expr(L, cnstr_rhs_expr(c));
    else if (is_level_eq_cnstr(c))
        return push_level(L, cnstr_rhs_level(c));
    else
        throw exception("arg #1 must be an equality/level constraint");
}
static int constraint_tostring(lua_State * L) {
    std::ostringstream out;
    out << to_constraint(L, 1);
    return push_string(L, out.str().c_str());
}
static int mk_eq_cnstr(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_constraint(L, mk_eq_cnstr(to_expr(L, 1), to_expr(L, 2),
                                          nargs >= 3 ? to_justification(L, 3) : justification()));
}
static int mk_level_eq_cnstr(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_constraint(L, mk_level_eq_cnstr(to_level_ext(L, 1), to_level_ext(L, 2),
                                                nargs == 3 ? to_justification(L, 3) : justification()));
}

static choice_fn to_choice_fn(lua_State * L, int idx) {
    luaL_checktype(L, idx, LUA_TFUNCTION); // user-fun
    luaref f(L, idx);
    return choice_fn([=](expr const & mvar, expr const & mvar_type, substitution const & s, name_generator const & ngen) {
            lua_State * L = f.get_state();
            f.push();
            push_expr(L, mvar);
            push_expr(L, mvar_type);
            push_substitution(L, s);
            push_name_generator(L, ngen);
            pcall(L, 4, 1, 0);
            buffer<constraints> r;
            if (lua_isnil(L, -1)) {
                // do nothing
            } else if (lua_istable(L, -1)) {
                int num = objlen(L, -1);
                // each entry is an alternative
                for (int i = 1; i <= num; i++) {
                    lua_rawgeti(L, -1, i);
                    if (is_constraint(L, -1))
                        r.push_back(constraints(to_constraint(L, -1)));
                    else if (is_expr(L, -1))
                        r.push_back(constraints(mk_eq_cnstr(mvar, to_expr(L, -1), justification())));
                    else
                        r.push_back(to_list_constraint_ext(L, -1));
                    lua_pop(L, 1);
                }
            } else {
                throw exception("invalid choice function, result must be an array of triples");
            }
            lua_pop(L, 1);
            return to_lazy(to_list(r.begin(), r.end()));
        });
}

static int mk_choice_cnstr(lua_State * L) {
    int nargs = lua_gettop(L);
    expr m           = to_expr(L, 1);
    choice_fn fn     = to_choice_fn(L, 2);
    if (nargs == 2)
        return push_constraint(L, mk_choice_cnstr(m, fn, 0, false, justification()));
    else if (nargs == 3 && is_justification(L, 3))
        return push_constraint(L, mk_choice_cnstr(m, fn, 0, false, to_justification(L, 3)));
    else if (nargs == 3)
        return push_constraint(L, mk_choice_cnstr(m, fn, lua_tonumber(L, 3), false, justification()));
    else if (nargs == 4)
        return push_constraint(L, mk_choice_cnstr(m, fn, lua_tonumber(L, 3), lua_toboolean(L, 4), justification()));
    else
        return push_constraint(L, mk_choice_cnstr(m, fn, lua_tonumber(L, 3), lua_toboolean(L, 4),
                                                  to_justification(L, 5)));
}

static int constraint_expr(lua_State * L) {
    constraint const & c = to_constraint(L, 1);
    if (is_choice_cnstr(c))
        return push_expr(L, cnstr_expr(c));
    else
        throw exception("arg #1 must be a choice constraint");
}

static int constraint_delay_factor(lua_State * L) {
    constraint const & c = to_constraint(L, 1);
    if (is_choice_cnstr(c))
        return push_integer(L, cnstr_delay_factor(c));
    else
        throw exception("arg #1 must be a choice constraint");
}

static const struct luaL_Reg constraint_m[] = {
    {"__gc",            constraint_gc}, // never throws
    {"__tostring",      safe_function<constraint_tostring>},
    {"is_eq",           safe_function<constraint_is_eq_cnstr>},
    {"is_level_eq",     safe_function<constraint_is_level_eq_cnstr>},
    {"is_choice",       safe_function<constraint_is_choice_cnstr>},
    {"is_eqp",          safe_function<constraint_is_eqp>},
    {"kind",            safe_function<constraint_get_kind>},
    {"lhs",             safe_function<constraint_lhs>},
    {"rhs",             safe_function<constraint_rhs>},
    {"justification",   safe_function<constraint_jst>},
    {"expr",            safe_function<constraint_expr>},
    {"delay_factor",    safe_function<constraint_delay_factor>},
    {0, 0}
};

// Constraint sequences
DECL_UDATA(constraint_seq)

static int constraint_seq_mk(lua_State * L) {
    unsigned nargs = lua_gettop(L);
    constraint_seq cs;
    for (unsigned i = 0; i < nargs; i++) {
        cs += to_constraint(L, i);
    }
    return push_constraint_seq(L, cs);
}

static int constraint_seq_concat(lua_State * L) {
    if (is_constraint_seq(L, 1) && is_constraint(L, 2))
        return push_constraint_seq(L, to_constraint_seq(L, 1) + to_constraint(L, 2));
    else
        return push_constraint_seq(L, to_constraint_seq(L, 1) + to_constraint_seq(L, 2));
}

static int constraint_seq_linearize(lua_State * L) {
    buffer<constraint> tmp;
    to_constraint_seq(L, 1).linearize(tmp);
    lua_newtable(L);
    int i = 1;
    for (constraint const & c : tmp) {
        push_constraint(L, c);
        lua_rawseti(L, -2, i);
        i++;
    }
    return 1;
}

static const struct luaL_Reg constraint_seq_m[] = {
    {"__gc",            constraint_seq_gc},
    {"__concat",        constraint_seq_concat},
    {"concat",          constraint_seq_concat},
    {"linearize",       constraint_seq_linearize},
    {0, 0}
};

static void open_constraint(lua_State * L) {
    luaL_newmetatable(L, constraint_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, constraint_m, 0);

    luaL_newmetatable(L, constraint_seq_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, constraint_seq_m, 0);

    SET_GLOBAL_FUN(constraint_pred,   "is_constraint");
    SET_GLOBAL_FUN(mk_eq_cnstr,       "mk_eq_cnstr");
    SET_GLOBAL_FUN(mk_level_eq_cnstr, "mk_level_eq_cnstr");
    SET_GLOBAL_FUN(mk_choice_cnstr,   "mk_choice_cnstr");

    lua_newtable(L);
    SET_ENUM("Eq",          constraint_kind::Eq);
    SET_ENUM("LevelEq",     constraint_kind::LevelEq);
    SET_ENUM("Choice",      constraint_kind::Choice);
    lua_setglobal(L, "constraint_kind");

    SET_GLOBAL_FUN(constraint_seq_pred, "is_constraint_seq");
    SET_GLOBAL_FUN(constraint_seq_mk,   "constraint_seq");
}

// Substitution
DECL_UDATA(substitution)
static int mk_substitution(lua_State * L) { return push_substitution(L, substitution()); }
static int subst_assign(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 3) {
        if (is_expr(L, 3)) {
            if (is_expr(L, 2))
                to_substitution(L, 1).assign(to_expr(L, 2), to_expr(L, 3));
            else
                to_substitution(L, 1).assign(to_name_ext(L, 2), to_expr(L, 3));
        } else {
            if (is_level(L, 2))
                to_substitution(L, 1).assign(to_level(L, 2), to_level(L, 3));
            else
                to_substitution(L, 1).assign(to_name_ext(L, 2), to_level(L, 3));
        }
    } else {
        if (is_expr(L, 3)) {
            if (is_expr(L, 2))
                to_substitution(L, 1).assign(to_expr(L, 2), to_expr(L, 3), to_justification(L, 4));
            else
                to_substitution(L, 1).assign(to_name_ext(L, 2), to_expr(L, 3), to_justification(L, 4));
        } else {
            if (is_level(L, 2))
                to_substitution(L, 1).assign(to_level(L, 2), to_level(L, 3), to_justification(L, 4));
            else
                to_substitution(L, 1).assign(to_name_ext(L, 2), to_level(L, 3), to_justification(L, 4));
        }
    }
    return 0;
}
static int subst_is_assigned(lua_State * L) {
    if (is_expr(L, 2))
        return push_boolean(L, to_substitution(L, 1).is_assigned(to_expr(L, 2)));
    else
        return push_boolean(L, to_substitution(L, 1).is_assigned(to_level(L, 2)));
}
static int subst_is_expr_assigned(lua_State * L) { return push_boolean(L, to_substitution(L, 1).is_expr_assigned(to_name_ext(L, 2))); }
static int subst_is_level_assigned(lua_State * L) { return push_boolean(L, to_substitution(L, 1).is_level_assigned(to_name_ext(L, 2))); }
static int subst_occurs(lua_State * L) { return push_boolean(L, to_substitution(L, 1).occurs(to_expr(L, 2), to_expr(L, 3))); }
static int subst_occurs_expr(lua_State * L) { return push_boolean(L, to_substitution(L, 1).occurs_expr(to_name_ext(L, 2), to_expr(L, 3))); }
static int subst_instantiate(lua_State * L) {
    if (is_expr(L, 2)) {
        auto r = to_substitution(L, 1).instantiate_metavars(to_expr(L, 2));
        push_expr(L, r.first); push_justification(L, r.second);
    } else {
        auto r = to_substitution(L, 1).instantiate_metavars(to_level(L, 2));
        push_level(L, r.first); push_justification(L, r.second);
    }
    return 2;
}

static int subst_instantiate_all(lua_State * L) {
    auto r = to_substitution(L, 1).instantiate_metavars_all(to_expr(L, 2));
    push_expr(L, r.first); push_justification(L, r.second);
    return 2;
}

static int subst_for_each_expr(lua_State * L) {
    substitution const & s = to_substitution(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    s.for_each_expr([&](name const & n, expr const & e, justification const & j) {
            lua_pushvalue(L, 2); // push user-fun
            push_name(L, n); push_expr(L, e); push_justification(L, j);
            pcall(L, 3, 0, 0);
        });
    return 0;
}

static int subst_for_each_level(lua_State * L) {
    substitution const & s = to_substitution(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    s.for_each_level([&](name const & n, level const & l, justification const & j) {
            lua_pushvalue(L, 2); // push user-fun
            push_name(L, n); push_level(L, l); push_justification(L, j);
            pcall(L, 3, 0, 0);
        });
    return 0;
}

static int subst_copy(lua_State * L) {
    return push_substitution(L, substitution(to_substitution(L, 1)));
}

static const struct luaL_Reg substitution_m[] = {
    {"__gc",                   substitution_gc},
    {"copy",                   safe_function<subst_copy>},
    {"assign",                 safe_function<subst_assign>},
    {"is_assigned",            safe_function<subst_is_assigned>},
    {"is_expr_assigned",       safe_function<subst_is_expr_assigned>},
    {"is_level_assigned",      safe_function<subst_is_level_assigned>},
    {"occurs",                 safe_function<subst_occurs>},
    {"occurs_expr",            safe_function<subst_occurs_expr>},
    {"instantiate",            safe_function<subst_instantiate>},
    {"instantiate_all",        safe_function<subst_instantiate_all>},
    {"for_each_expr",          safe_function<subst_for_each_expr>},
    {"for_each_level",         safe_function<subst_for_each_level>},
    {0, 0}
};

static void open_substitution(lua_State * L) {
    luaL_newmetatable(L, substitution_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, substitution_m, 0);

    SET_GLOBAL_FUN(mk_substitution, "substitution");
    SET_GLOBAL_FUN(substitution_pred, "is_substitution");
}

// type_checker
DECL_UDATA(type_checker_ref)

static int mk_type_checker(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1) {
        return push_type_checker_ref(L, std::make_shared<type_checker>(to_environment(L, 1)));
    } else {
        return push_type_checker_ref(L, std::make_shared<type_checker>(to_environment(L, 1),
                                                                       to_name_generator(L, 2).mk_child()));
    }
}
static int type_checker_whnf(lua_State * L) { return push_ecs(L, to_type_checker_ref(L, 1)->whnf(to_expr(L, 2))); }
static int type_checker_ensure_pi(lua_State * L) {
    if (lua_gettop(L) == 2)
        return push_ecs(L, to_type_checker_ref(L, 1)->ensure_pi(to_expr(L, 2)));
    else
        return push_ecs(L, to_type_checker_ref(L, 1)->ensure_pi(to_expr(L, 2), to_expr(L, 3)));
}
static int type_checker_ensure_sort(lua_State * L) {
    if (lua_gettop(L) == 2)
        return push_ecs(L, to_type_checker_ref(L, 1)->ensure_sort(to_expr(L, 2)));
    else
        return push_ecs(L, to_type_checker_ref(L, 1)->ensure_sort(to_expr(L, 2), to_expr(L, 3)));
}
static int type_checker_check(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs <= 2)
        return push_ecs(L, to_type_checker_ref(L, 1)->check(to_expr(L, 2), level_param_names()));
    else
        return push_ecs(L, to_type_checker_ref(L, 1)->check(to_expr(L, 2), to_level_param_names(L, 3)));
}
static int type_checker_infer(lua_State * L) { return push_ecs(L, to_type_checker_ref(L, 1)->infer(to_expr(L, 2))); }

static int type_checker_is_def_eq(lua_State * L) { return push_bcs(L, to_type_checker_ref(L, 1)->is_def_eq(to_expr(L, 2), to_expr(L, 3))); }
static int type_checker_is_prop(lua_State * L) { return push_bcs(L, to_type_checker_ref(L, 1)->is_prop(to_expr(L, 2))); }

static name * g_tmp_prefix = nullptr;

static int mk_type_checker_with_hints(lua_State * L) {
    environment const & env = to_environment(L, 1);
    int nargs = lua_gettop(L);
    if (nargs == 1) {
        return push_type_checker_ref(L, mk_type_checker(env, name_generator(*g_tmp_prefix)));
    } else {
        return push_type_checker_ref(L, mk_type_checker(env, to_name_generator(L, 2).mk_child()));
    }
}

static const struct luaL_Reg type_checker_ref_m[] = {
    {"__gc",        type_checker_ref_gc},
    {"whnf",        safe_function<type_checker_whnf>},
    {"ensure_pi",   safe_function<type_checker_ensure_pi>},
    {"ensure_sort", safe_function<type_checker_ensure_sort>},
    {"check",       safe_function<type_checker_check>},
    {"infer",       safe_function<type_checker_infer>},
    {"is_def_eq",   safe_function<type_checker_is_def_eq>},
    {"is_prop",     safe_function<type_checker_is_prop>},
    {0, 0}
};

// type_check procedure
static int type_check(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2) {
        return push_certified_declaration(L, check(to_environment(L, 1), to_declaration(L, 2)));
    } else {
        return push_certified_declaration(L, check(to_environment(L, 1), to_declaration(L, 2),
                                                   to_name_generator(L, 3).mk_child()));
    }
}

static int add_declaration(lua_State * L) {
    int nargs = lua_gettop(L);
    optional<certified_declaration> d;
    environment const & env = to_environment(L, 1);
    if (nargs == 2) {
        d = check(env, unfold_untrusted_macros(env, to_declaration(L, 2)));
    } else {
        d = check(env, unfold_untrusted_macros(env, to_declaration(L, 2)), to_name_generator(L, 3).mk_child());
    }
    return push_environment(L, module::add(to_environment(L, 1), *d));
}

static void open_type_checker(lua_State * L) {
    luaL_newmetatable(L, type_checker_ref_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, type_checker_ref_m, 0);

    SET_GLOBAL_FUN(mk_type_checker, "type_checker");
    SET_GLOBAL_FUN(mk_type_checker_with_hints, "type_checker_with_hints");
    SET_GLOBAL_FUN(type_checker_ref_pred, "is_type_checker");
    SET_GLOBAL_FUN(type_check, "type_check");
    SET_GLOBAL_FUN(type_check, "check");
    SET_GLOBAL_FUN(add_declaration, "add_decl");
}

namespace inductive {
/** \brief Get the number of indices (if available), if they are, increment idx */
static unsigned get_num_params(lua_State * L, int & idx) {
    if (lua_isnumber(L, idx)) {
        if (lua_tonumber(L, idx) < 0)
            throw exception(sstream() << "arg #" << idx << " (number of parameters) must be nonnegative");
        unsigned r = lua_tonumber(L, idx);
        idx++;
        return r;
    } else {
        return 0;
    }
}
static int add_inductive1(lua_State * L) {
    environment env      = to_environment(L, 1);
    name const & Iname   = to_name_ext(L, 2);
    int idx = 3;
    level_param_names ls;
    if (!is_expr(L, idx) && !lua_isnumber(L, idx)) {
        ls = to_level_param_names(L, idx);
        idx++;
    }
    unsigned num_params = get_num_params(L, idx);
    expr Itype          = to_expr(L, idx);
    int nargs = lua_gettop(L);
    buffer<intro_rule> irules;
    for (int i = idx+1; i <= nargs; i+=2)
        irules.push_back(intro_rule(to_name_ext(L, i), to_expr(L, i+1)));
    return push_environment(L, module::add_inductive(env, Iname, ls, num_params, Itype, to_list(irules.begin(), irules.end())));
}
static int add_inductivek(lua_State * L) {
    environment env      = to_environment(L, 1);
    level_param_names ls = to_level_param_names(L, 2);
    int idx = 3;
    unsigned num_params  = get_num_params(L, idx);
    int nargs = lua_gettop(L);
    buffer<inductive_decl> decls;
    for (; idx <= nargs; idx++) {
        luaL_checktype(L, idx, LUA_TTABLE);
        int decl_sz = objlen(L, idx);
        if (decl_sz < 2)
            throw exception("invalid add_inductive, datatype declaration must have at least a name and type");
        if (decl_sz % 2 != 0)
            throw exception("invalid add_inductive, datatype declaration must have an even number of fields: (name, type)+");
        lua_rawgeti(L, idx, 1);
        lua_rawgeti(L, idx, 2);
        name Iname = to_name_ext(L, -2);
        expr Itype = to_expr(L, -1);
        lua_pop(L, 2);
        buffer<intro_rule> irules;
        for (int i = 3; i <= decl_sz; i+=2) {
            lua_rawgeti(L, idx, i);
            lua_rawgeti(L, idx, i+1);
            irules.push_back(intro_rule(to_name_ext(L, -2), to_expr(L, -1)));
            lua_pop(L, 2);
        }
        decls.push_back(inductive_decl(Iname, Itype, to_list(irules.begin(), irules.end())));
    }
    if (decls.empty())
        throw exception("invalid add_inductive, at least one inductive type must be defined");
    return push_environment(L, module::add_inductive(env, ls, num_params, to_list(decls.begin(), decls.end())));
}
static int add_inductive(lua_State * L) {
    if (is_name(L, 2) || lua_isstring(L, 2))
        return add_inductive1(L);
    else
        return add_inductivek(L);
}
}

static void open_inductive(lua_State * L) {
    SET_GLOBAL_FUN(inductive::add_inductive, "add_inductive");
}

void open_kernel_module(lua_State * L) {
    open_level(L);
    open_list_level(L);
    open_binder_info(L);
    open_expr(L);
    open_list_expr(L);
    open_macro_definition(L);
    open_declaration(L);
    open_formatter(L);
    open_environment_id(L);
    open_certified_declaration(L);
    open_list_certified_declaration(L);
    open_environment(L);
    open_io_state(L);
    open_justification(L);
    open_constraint(L);
    open_list_constraint(L);
    open_substitution(L);
    open_type_checker(L);
    open_inductive(L);
}

void initialize_kernel_bindings() {
    g_print_formatter_factory = new formatter_factory(mk_print_formatter_factory());
    g_print_mutex             = new mutex();
    g_tmp_prefix              = new name(name::mk_internal_unique_name());
}
void finalize_kernel_bindings() {
    delete g_tmp_prefix;
    delete g_print_mutex;
    delete g_print_formatter_factory;
}
}
