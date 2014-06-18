/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/list.h"
#include "util/sstream.h"

namespace lean {
/** \brief Convert a Lua table into a list<T> */
template<typename T, typename Proc>
list<T> table_to_list(lua_State * L, int idx, Proc const & to_value) {
    if (lua_istable(L, idx)) {
        int n = objlen(L, idx);
        list<T> r;
        for (int i = n; i >= 1; i--) {
            lua_rawgeti(L, idx, i);
            r = cons(to_value(L, -1), r);
            lua_pop(L, 1);
        }
        return r;
    } else {
        throw exception(sstream() << "arg #" << idx << " must be a lua table");
    }
}

#define DEFINE_LUA_LIST(T, PushVal, ToVal)                              \
typedef list<T> list_ ## T;                                             \
DECL_UDATA(list_ ## T)                                                  \
static int list_ ## T ## _cons(lua_State * L) { return push_list_ ## T(L, list<T>(ToVal(L, 1), to_list_ ## T(L, 2))); } \
static int list_ ## T ## _nil(lua_State * L) { return push_list_ ## T(L, list<T>()); } \
static int list_ ## T ## _mk(lua_State * L) {                           \
    int nargs = lua_gettop(L);                                          \
    return (nargs == 0) ? list_ ## T ## _nil(L) : list_ ## T ## _cons(L); \
}                                                                       \
static int list_ ## T ## _is_nil(lua_State * L) { return push_boolean(L, is_nil(to_list_ ## T(L, 1))); } \
static int list_ ## T ## _car(lua_State * L) {                          \
    list<T> & l = to_list_ ## T(L, 1);                                  \
    if (is_nil(l)) throw exception("arg #1 must be a cons cell");       \
    return PushVal(L, car(l));                                          \
}                                                                       \
static int list_ ## T ## _cdr(lua_State * L) {                          \
    list<T> & l = to_list_ ## T(L, 1);                                  \
    if (is_nil(l)) throw exception("arg #1 must be a cons cell");       \
    return push_list_ ## T(L, cdr(l));                                  \
}                                                                       \
static int list_ ## T ## _eq(lua_State * L) { return push_boolean(L, to_list_ ## T(L, 1) == to_list_ ## T(L, 2)); } \
static int list_ ## T ## _is_eqp(lua_State * L) { return push_boolean(L, is_eqp(to_list_ ## T(L, 1), to_list_ ## T(L, 2))); } \
static int list_ ## T ## _len(lua_State * L) { return push_integer(L, length(to_list_ ## T(L, 1))); } \
static const struct luaL_Reg list_ ## T ## _m[] = {                     \
    {"__gc",            list_ ## T ## _gc},                             \
    {"__eq",            safe_function<list_ ## T ## _eq>},              \
    {"__len",           safe_function<list_ ## T ## _len>},             \
    {"is_nil",          safe_function<list_ ## T ## _is_nil>},          \
    {"empty",           safe_function<list_ ## T ## _is_nil>},          \
    {"car",             safe_function<list_ ## T ## _car>},             \
    {"cdr",             safe_function<list_ ## T ## _cdr>},             \
    {"head",            safe_function<list_ ## T ## _car>},             \
    {"tail",            safe_function<list_ ## T ## _cdr>},             \
    {"is_eqp",          safe_function<list_ ## T ## _is_eqp>},          \
    {0, 0}                                                              \
};                                                                      \
list<T> to_list_ ## T ## _ext(lua_State * L, int idx) {                 \
    if (is_list_ ## T(L, idx))                                          \
        return to_list_ ## T(L, idx);                                   \
    else                                                                \
        return table_to_list<T>(L, idx, ToVal);                         \
}                                                                       \
static void open_list_ ## T(lua_State * L) {                            \
    luaL_newmetatable(L, list_ ## T ## _mt);                            \
    lua_pushvalue(L, -1);                                               \
    lua_setfield(L, -2, "__index");                                     \
    setfuncs(L, list_ ## T ## _m, 0);                                   \
                                                                        \
    set_global_function<list_ ## T ## _mk>(L, "list_" #T);              \
    set_global_function<list_ ## T ## _pred>(L, "is_list_" #T);         \
}
}
