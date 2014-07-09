/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lua.hpp>

namespace lean {
// =======================================
// Lua 5.1 and 5.2 compatibility
//
// The following helper functions make sure
// we can compile using Lua 5.1 or 5.2
void setfuncs(lua_State * L, luaL_Reg const * l, int nup);
bool testudata(lua_State * L, int idx, char const * mt);
int load(lua_State * L, lua_Reader reader, void * data, char const * source);
size_t objlen(lua_State * L, int idx);
void dofile(lua_State * L, char const * fname);
void dostring(lua_State * L, char const * str);
void pcall(lua_State * L, int nargs, int nresults, int errorfun);
char const * tostring (lua_State * L, int idx);
/**
    \brief Return true iff coroutine is done, false if it has yielded,
    and throws an exception if error.
*/
bool resume(lua_State * L, int nargs);
int lessthan(lua_State * L, int idx1, int idx2);
int equal(lua_State * L, int idx1, int idx2);
int get_nonnil_top(lua_State * L);
// =======================================

// =======================================
// Goodies/Macros for automating Lua binding
// generation.
/**
   \brief Wrapper for invoking function f, and catching Lean exceptions.
*/
int safe_function_wrapper(lua_State * L, lua_CFunction f);
template<lua_CFunction F> int safe_function(lua_State * L) {
    return safe_function_wrapper(L, F);
}
template<lua_CFunction F> void set_global_function(lua_State * L, char const * name) {
    lua_pushcfunction(L, safe_function<F>);
    lua_setglobal(L, name);
}
#define SET_GLOBAL_FUN(F, N) set_global_function<F>(L, N)
#define SET_FUN(F, N) lua_pushstring(L, N); lua_pushcfunction(L, safe_function<F>); lua_settable(L, -3)

// Auxiliary macro for creating a Lua table that stores enumeration values
#define SET_ENUM(N, V) lua_pushstring(L, N); lua_pushinteger(L, static_cast<int>(V)); lua_settable(L, -3)

#define DECL_PUSH_CORE(NAME, T, TREF)           \
int push_ ## NAME(lua_State * L, TREF val) {    \
    void * mem = lua_newuserdata(L, sizeof(T)); \
    new (mem) T(val);                           \
    luaL_getmetatable(L, NAME ## _mt);          \
    lua_setmetatable(L, -2);                    \
    return 1;                                   \
}

#define DECL_PUSH(T)                             \
DECL_PUSH_CORE(T, T, T const &)                  \
DECL_PUSH_CORE(T, T, T &&)

#define DECL_GC(T) static int T ## _gc(lua_State * L) { static_cast<T*>(lua_touserdata(L, 1))->~T(); return 0; }

#define DECL_PRED(T)                                                    \
bool is_ ## T(lua_State * L, int idx) { return testudata(L, idx, T ## _mt); } \
static int T ## _pred(lua_State * L) { check_num_args(L, 1); return push_boolean(L, is_ ## T(L, 1)); }

void throw_bad_arg_error(lua_State * L, int i, char const * expected_type);

/**
   \brief Create basic declarations for adding a new kind of userdata in Lua
   T is a Lean object type.
   For example, if T == expr, it produces an implementation for the
   following declarations

     constexpr char const * expr_mt = "expr";
     expr & to_expr(lua_State * L, int i);
     bool is_expr(lua_State * L, int i);
     static int expr_pred(lua_State * L);
     static int expr_gc(lua_State * L);
     int push_expr(lua_State * L, expr const & e);
     int push_expr(lua_State * L, expr && e);
*/
#define DECL_UDATA(T)                                                   \
constexpr char const * T ## _mt = #T;                                   \
DECL_PRED(T)                                                            \
T & to_ ## T(lua_State * L, int i) { if (!is_ ## T(L, i)) throw_bad_arg_error(L, i, T ## _mt); return *static_cast<T*>(luaL_checkudata(L, i, T ## _mt)); } \
DECL_GC(T)                                                              \
DECL_PUSH(T)

/**
   \brief Similar to DECL_UDATA, but it only declares the functions.

   For example, if T == expr, it produces the following declarations:

      class expr;
      expr & to_expr(lua_State * L, int i);
      bool is_expr(lua_State * L, int i);
      int push_expr(lua_State * L, expr const & e);
      int push_expr(lua_State * L, expr && e);
*/
#define UDATA_DEFS_CORE(T)                      \
T & to_ ## T(lua_State * L, int i);             \
bool is_ ## T(lua_State * L, int i);            \
int push_ ## T(lua_State * L, T const & e);     \
int push_ ## T(lua_State * L, T && e);
#define UDATA_DEFS(T)                           \
class T;                                        \
UDATA_DEFS_CORE(T)
// =======================================

// =======================================
// Useful macros
inline int push_boolean(lua_State * L, bool b) { lua_pushboolean(L, b); return 1; }
inline int push_string(lua_State * L, char const * s) { lua_pushstring(L, s); return 1; }
inline int push_integer(lua_State * L, lua_Integer v) { lua_pushinteger(L, v); return 1; }
inline int push_number(lua_State * L, lua_Number v) { lua_pushnumber(L, v); return 1; }
inline int push_nil(lua_State * L) { lua_pushnil(L); return 1; }
// =======================================

// =======================================
// Extra validation functions

/** \brief Throw an exception if lua_gettop(L) != num */
void check_num_args(lua_State * L, int num);
/** \brief Throw an exception if lua_gettop(L) > high */
void check_atmost_num_args(lua_State * L, int high);
/** \brief Throw an exception if lua_gettop(L) < low */
void check_atleast_num_args(lua_State * L, int low);
// =======================================
}
