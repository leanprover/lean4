/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "util/debug.h"
#include "util/sstream.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"
#include "bindings/lua/util.h"

namespace lean {
DECL_UDATA(mpz)

template<unsigned idx>
static mpz const & to_mpz(lua_State * L) {
    static thread_local mpz arg;
    switch (lua_type(L, idx)) {
    case LUA_TNUMBER:       arg = static_cast<long>(lua_tointeger(L, idx)); return arg;
    case LUA_TSTRING:       arg = mpz(lua_tostring(L, idx)); return arg;
    case LUA_TUSERDATA:     return *static_cast<mpz*>(luaL_checkudata(L, idx, mpz_mt));
    default: throw exception(sstream() << "arg #" << idx << " must be a number, string or mpz");
    }
}

mpz to_mpz_ext(lua_State * L, int idx) {
    switch (lua_type(L, idx)) {
    case LUA_TNUMBER:       return mpz(static_cast<long>(lua_tointeger(L, idx)));
    case LUA_TSTRING:       return mpz(lua_tostring(L, idx));
    case LUA_TUSERDATA:     return *static_cast<mpz*>(luaL_checkudata(L, idx, mpz_mt));
    default: throw exception(sstream() << "arg #" << idx << " must be a number, string or mpz");
    }
}

static int mpz_tostring(lua_State * L) {
    mpz * n = static_cast<mpz*>(luaL_checkudata(L, 1, mpz_mt));
    std::ostringstream out;
    out << *n;
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int mpz_eq(lua_State * L) {
    lua_pushboolean(L, to_mpz<1>(L) == to_mpz<2>(L));
    return 1;
}

static int mpz_lt(lua_State * L) {
    lua_pushboolean(L, to_mpz<1>(L) < to_mpz<2>(L));
    return 1;
}

static int mpz_add(lua_State * L) {
    return push_mpz(L, to_mpz<1>(L) + to_mpz<2>(L));
}

static int mpz_sub(lua_State * L) {
    return push_mpz(L, to_mpz<1>(L) - to_mpz<2>(L));
}

static int mpz_mul(lua_State * L) {
    return push_mpz(L, to_mpz<1>(L) * to_mpz<2>(L));
}

static int mpz_div(lua_State * L) {
    mpz const & arg2 = to_mpz<2>(L);
    if (arg2 == 0) throw exception("division by zero");
    return push_mpz(L, to_mpz<1>(L) / arg2);
}

static int mpz_umn(lua_State * L) {
    return push_mpz(L, 0 - to_mpz<1>(L));
}

static int mpz_power(lua_State * L) {
    int k = luaL_checkinteger(L, 2);
    if (k < 0) throw exception("argument #2 must be positive");
    return push_mpz(L, pow(to_mpz<1>(L), k));
}

static int mk_mpz(lua_State * L) {
    mpz const & arg = to_mpz<1>(L);
    return push_mpz(L, arg);
}

static const struct luaL_Reg mpz_m[] = {
    {"__gc",       mpz_gc}, // never throws
    {"__tostring", safe_function<mpz_tostring>},
    {"__eq",       safe_function<mpz_eq>},
    {"__lt",       safe_function<mpz_lt>},
    {"__add",      safe_function<mpz_add>},
    {"__sub",      safe_function<mpz_sub>},
    {"__mul",      safe_function<mpz_mul>},
    {"__div",      safe_function<mpz_div>},
    {"__pow",      safe_function<mpz_power>},
    {"__unm",      safe_function<mpz_umn>},
    {0, 0}
};

void open_mpz(lua_State * L) {
    luaL_newmetatable(L, mpz_mt);
    setfuncs(L, mpz_m, 0);

    SET_GLOBAL_FUN(mk_mpz,   "mpz");
    SET_GLOBAL_FUN(mpz_pred, "is_mpz");
}

DECL_UDATA(mpq)

template<unsigned idx>
static mpq const & to_mpq(lua_State * L) {
    static thread_local mpq arg;
    switch (lua_type(L, idx)) {
    case LUA_TNUMBER:       arg = lua_tonumber(L, idx); return arg;
    case LUA_TSTRING:       arg = mpq(lua_tostring(L, idx)); return arg;
    case LUA_TUSERDATA:
        if (is_mpz(L, idx)) {
            arg = mpq(to_mpz<idx>(L));
            return arg;
        } else {
            return *static_cast<mpq*>(luaL_checkudata(L, idx, mpq_mt));
        }
    default: throw exception(sstream() << "arg #" << idx << " must be a number, string, mpz or mpq");
    }
}

mpq to_mpq_ext(lua_State * L, int idx) {
    switch (lua_type(L, idx)) {
    case LUA_TNUMBER:       return mpq(lua_tonumber(L, idx));
    case LUA_TSTRING:       return mpq(lua_tostring(L, idx));
    case LUA_TUSERDATA:
        if (is_mpz(L, idx)) {
            return mpq(to_mpz<1>(L));
        } else {
            return *static_cast<mpq*>(luaL_checkudata(L, idx, mpq_mt));
        }
    default: throw exception(sstream() << "arg #" << idx << " must be a number, string, mpz or mpq");
    }
}

static int mpq_tostring(lua_State * L) {
    mpq * n = static_cast<mpq*>(luaL_checkudata(L, 1, mpq_mt));
    std::ostringstream out;
    out << *n;
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int mpq_eq(lua_State * L) {
    lua_pushboolean(L, to_mpq<1>(L) == to_mpq<2>(L));
    return 1;
}

static int mpq_lt(lua_State * L) {
    lua_pushboolean(L, to_mpq<1>(L) < to_mpq<2>(L));
    return 1;
}

static int mpq_add(lua_State * L) {
    return push_mpq(L, to_mpq<1>(L) + to_mpq<2>(L));
}

static int mpq_sub(lua_State * L) {
    return push_mpq(L, to_mpq<1>(L) - to_mpq<2>(L));
}

static int mpq_mul(lua_State * L) {
    return push_mpq(L, to_mpq<1>(L) * to_mpq<2>(L));
}

static int mpq_div(lua_State * L) {
    mpq const & arg2 = to_mpq<2>(L);
    if (arg2 == 0) throw exception("division by zero");
    return push_mpq(L, to_mpq<1>(L) / arg2);
}

static int mpq_umn(lua_State * L) {
    return push_mpq(L, 0 - to_mpq<1>(L));
}

static int mpq_power(lua_State * L) {
    int k = luaL_checkinteger(L, 2);
    if (k < 0) throw exception("argument #2 must be positive");
    return push_mpq(L, pow(to_mpq<1>(L), k));
}

static int mk_mpq(lua_State * L) {
    mpq const & arg = to_mpq<1>(L);
    return push_mpq(L, arg);
}

static const struct luaL_Reg mpq_m[] = {
    {"__gc",       mpq_gc}, // never throws
    {"__tostring", safe_function<mpq_tostring>},
    {"__eq",       safe_function<mpq_eq>},
    {"__lt",       safe_function<mpq_lt>},
    {"__add",      safe_function<mpq_add>},
    {"__sub",      safe_function<mpq_sub>},
    {"__mul",      safe_function<mpq_mul>},
    {"__div",      safe_function<mpq_div>},
    {"__pow",      safe_function<mpq_power>},
    {"__unm",      safe_function<mpq_umn>},
    {0, 0}
};

void open_mpq(lua_State * L) {
    luaL_newmetatable(L, mpq_mt);
    setfuncs(L, mpq_m, 0);

    SET_GLOBAL_FUN(mk_mpq,   "mpq");
    SET_GLOBAL_FUN(mpq_pred, "is_mpq");
}
}
