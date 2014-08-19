/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/sstream.h"

namespace lean {
#define DEFINE_LUA_PAIR_CORE(T1, PushVal1, ToVal1, T2, PushVal2, ToVal2, MK_Name, IS_Name) \
typedef pair<T1, T2> pair_ ## T1 ## _ ## T2;                            \
DECL_UDATA(pair_ ## T1 ## _ ## T2)                                      \
pair<T1, T2> to_pair_ ## T1 ## _ ## T2 ## _ext(lua_State * L, int idx) { \
    if (is_pair_ ## T1 ## _ ## T2(L, idx)) {                            \
        return to_pair_ ## T1 ## _ ## T2(L, idx);                       \
    } else if (lua_istable(L, idx)) {                                   \
        lua_pushvalue(L, idx);                                          \
        int n = objlen(L, -1);                                          \
        if (n != 2)                                                     \
            throw exception(sstream() << "arg #" << idx << " must be a table of size 2"); \
        lua_rawgeti(L, -1, 1);                                          \
        lua_rawgeti(L, -2, 2);                                          \
        pair<T1, T2> r(ToVal1(L, -2), ToVal2(L, -1));                   \
        lua_pop(L, 3);                                                  \
        return r;                                                       \
    } else {                                                            \
        throw exception(sstream() << "arg #" << idx << " must be a pair or a Lua table"); \
    }                                                                   \
}                                                                       \
static int pair_ ## T1 ## _ ## T2 ## _mk(lua_State * L) { return push_pair_ ## T1 ## _ ## T2(L, pair<T1, T2>(ToVal1(L, 1), ToVal2(L, 2))); } \
static int pair_ ## T1 ## _ ## T2 ## _first(lua_State * L) { return PushVal1(L, to_pair_ ## T1 ## _ ## T2(L, 1).first); } \
static int pair_ ## T1 ## _ ## T2 ## _second(lua_State * L) { return PushVal2(L, to_pair_ ## T1 ## _ ## T2(L, 1).second); } \
static const struct luaL_Reg pair_ ## T1 ## _ ## T2 ## _m[] = {         \
    {"__gc",            pair_ ## T1 ## _ ## T2 ## _gc},                 \
    {"first",           safe_function<pair_ ## T1 ## _ ## T2 ## _first>}, \
    {"second",          safe_function<pair_ ## T1 ## _ ## T2 ## _second>}, \
    {0, 0}                                                              \
};                                                                      \
static void open_pair_ ## T1 ## _ ## T2 (lua_State * L) {               \
    luaL_newmetatable(L, pair_ ## T1 ## _ ## T2 ## _mt);                \
    lua_pushvalue(L, -1);                                               \
    lua_setfield(L, -2, "__index");                                     \
    setfuncs(L, pair_ ## T1 ## _ ## T2 ## _m, 0);                       \
                                                                        \
    set_global_function<pair_ ## T1 ## _ ## T2 ## _mk>(L, MK_Name);     \
    set_global_function<pair_ ## T1 ## _ ## T2 ## _pred>(L, IS_Name);   \
}

#define DEFINE_LUA_PAIR(T1, PushVal1, ToVal1, T2, PushVal2, ToVal2) DEFINE_LUA_PAIR_CORE(T1, PushVal1, ToVal1, T2, PushVal2, ToVal2, "pair_" #T1 "_" #T2, "is_pair_" #T1 "_" #T2)

// A Pair (T, T)
#define DEFINE_LUA_HOMO_PAIR(T, PushVal, ToVal) DEFINE_LUA_PAIR_CORE(T, PushVal, ToVal, T, PushVal, ToVal, "pair_" #T, "is_pair_" #T) \
static void open_pair_ ## T(lua_State * L) { open_pair_ ## T ## _ ## T(L); } \
pair<T, T> & to_pair_ ## T(lua_State * L, int idx) { return to_pair_ ## T ## _ ## T(L, idx); } \
pair<T, T> to_pair_ ## T ## _ext(lua_State * L, int idx) { return to_pair_ ## T ## _ ## T ## _ext(L, idx); } \
int push_pair_ ## T(lua_State * L, pair<T, T> const & p) { return push_pair_ ## T ## _ ## T(L, p); }
}
