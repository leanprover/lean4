/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "util/debug.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"
#include "bindings/lua/util.h"

namespace lean {
constexpr char const * mpz_mt = "mpz.mt";

template<unsigned idx>
static mpz const & to_mpz(lua_State * L) {
    static thread_local mpz arg;
    if (lua_isuserdata(L, idx)) {
        return *static_cast<mpz*>(luaL_checkudata(L, idx, mpz_mt));
    } else if (lua_isstring(L, idx)) {
        char const * str = luaL_checkstring(L, idx);
        arg = mpz(str);
        return arg;
    } else {
        arg = static_cast<long int>(luaL_checkinteger(L, 1));
        return arg;
    }
}

bool is_mpz(lua_State * L, int idx) {
    return testudata(L, idx, mpz_mt);
}

mpz & to_mpz(lua_State * L, int idx) {
    return *static_cast<mpz*>(luaL_checkudata(L, idx, mpz_mt));
}

int push_mpz(lua_State * L, mpz const & val) {
    void * mem = lua_newuserdata(L, sizeof(mpz));
    new (mem) mpz(val);
    luaL_getmetatable(L, mpz_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mpz_gc(lua_State * L) {
    mpz * n = static_cast<mpz*>(luaL_checkudata(L, 1, mpz_mt));
    n->~mpz();
    return 0;
}

static int mpz_tostring(lua_State * L) {
    mpz * n = static_cast<mpz*>(luaL_checkudata(L, 1, mpz_mt));
    std::ostringstream out;
    out << *n;
    lua_pushfstring(L, out.str().c_str());
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

static int mpz_pred(lua_State * L) {
    lua_pushboolean(L, is_mpz(L, 1));
    return 1;
}

static const struct luaL_Reg mpz_m[] = {
    {"__gc",       mpz_gc}, // never throws
    {"__tostring", safe_function<mpz_tostring>},
    {"__eq",       safe_function<mpz_eq>},
    {"__lt",       safe_function<mpz_lt>},
    {"__add",      safe_function<mpz_add>},
    {"__add",      safe_function<mpz_sub>},
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

constexpr char const * mpq_mt = "mpq.mt";

template<unsigned idx>
static mpq const & to_mpq(lua_State * L) {
    static thread_local mpq arg;
    if (lua_isuserdata(L, idx)) {
        return *static_cast<mpq*>(luaL_checkudata(L, idx, mpq_mt));
    } else if (lua_isstring(L, idx)) {
        char const * str = luaL_checkstring(L, idx);
        arg = mpq(str);
        return arg;
    } else {
        arg = static_cast<long int>(luaL_checkinteger(L, 1));
        return arg;
    }
}

bool is_mpq(lua_State * L, int idx) {
    return testudata(L, idx, mpq_mt);
}

mpq & to_mpq(lua_State * L, int idx) {
    return *static_cast<mpq*>(luaL_checkudata(L, idx, mpq_mt));
}

int push_mpq(lua_State * L, mpq const & val) {
    void * mem = lua_newuserdata(L, sizeof(mpq));
    new (mem) mpq(val);
    luaL_getmetatable(L, mpq_mt);
    lua_setmetatable(L, -2);
    return 1;
}

static int mpq_gc(lua_State * L) {
    mpq * n = static_cast<mpq*>(luaL_checkudata(L, 1, mpq_mt));
    n->~mpq();
    return 0;
}

static int mpq_tostring(lua_State * L) {
    mpq * n = static_cast<mpq*>(luaL_checkudata(L, 1, mpq_mt));
    std::ostringstream out;
    out << *n;
    lua_pushfstring(L, out.str().c_str());
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

static int mpq_pred(lua_State * L) {
    lua_pushboolean(L, is_mpq(L, 1));
    return 1;
}

static const struct luaL_Reg mpq_m[] = {
    {"__gc",       mpq_gc}, // never throws
    {"__tostring", safe_function<mpq_tostring>},
    {"__eq",       safe_function<mpq_eq>},
    {"__lt",       safe_function<mpq_lt>},
    {"__add",      safe_function<mpq_add>},
    {"__add",      safe_function<mpq_sub>},
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
