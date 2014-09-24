/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include "util/sstream.h"
#include "util/thread.h"
#include "util/numerics/mpz.h"

namespace lean {

unsigned mpz::log2() const {
    if (is_nonpos())
        return 0;
    unsigned r = mpz_sizeinbase(m_val, 2);
    lean_assert(r > 0);
    return r - 1;
}

unsigned mpz::mlog2() const {
    if (is_nonneg())
        return 0;
    mpz * _this = const_cast<mpz*>(this);
    _this->neg();
    lean_assert(is_pos());
    unsigned r = mpz_sizeinbase(m_val, 2);
    _this->neg();
    lean_assert(is_neg());
    return r - 1;
}

bool mpz::is_power_of_two(unsigned & shift) const {
    if (is_nonpos())
        return false;
    if (mpz_popcount(m_val) == 1) {
        shift = log2();
        return true;
    } else {
        return false;
    }
}

mpz operator%(mpz const & a, mpz const & b) {
    mpz r(rem(a, b));
    if (r.is_neg()) {
        if (b.is_pos())
            r += b;
        else
            r -= b;
    }
    return r;
}

bool root(mpz & root, mpz const & a, unsigned k) {
    mpz rem;
    mpz_rootrem(root.m_val, rem.m_val, a.m_val, k);
    return rem.is_zero();
}

void display(std::ostream & out, __mpz_struct const * v) {
    size_t sz = mpz_sizeinbase(v, 10) + 2;
    if (sz < 1024) {
        char buffer[1024];
        mpz_get_str(buffer, 10, v);
        out << buffer;
    } else {
        std::unique_ptr<char> buffer(new char[sz]);
        mpz_get_str(buffer.get(), 10, v);
        out << buffer.get();
    }
}

std::ostream & operator<<(std::ostream & out, mpz const & v) {
    display(out, v.m_val);
    return out;
}

static mpz * g_zero = nullptr;

mpz const & numeric_traits<mpz>::zero() {
    lean_assert(is_zero(*g_zero));
    return *g_zero;
}

void initialize_mpz() {
    g_zero = new mpz();
}

void finalize_mpz() {
    delete g_zero;
}

serializer & operator<<(serializer & s, mpz const & n) {
    std::ostringstream out;
    out << n;
    s << out.str();
    return s;
}

mpz read_mpz(deserializer & d) {
    return mpz(d.read_string().c_str());
}

DECL_UDATA(mpz)
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
    return push_string(L, out.str().c_str());
}

static int mpz_eq(lua_State * L) {
    return push_boolean(L, to_mpz_ext(L, 1) == to_mpz_ext(L, 2));
}

static int mpz_lt(lua_State * L) {
    return push_boolean(L, to_mpz_ext(L, 1) < to_mpz_ext(L, 2));
}

static int mpz_add(lua_State * L) {
    return push_mpz(L, to_mpz_ext(L, 1) + to_mpz_ext(L, 2));
}

static int mpz_sub(lua_State * L) {
    return push_mpz(L, to_mpz_ext(L, 1) - to_mpz_ext(L, 2));
}

static int mpz_mul(lua_State * L) {
    return push_mpz(L, to_mpz_ext(L, 1) * to_mpz_ext(L, 2));
}

static int mpz_div(lua_State * L) {
    mpz arg2 = to_mpz_ext(L, 2);
    if (arg2 == 0) throw exception("division by zero");
    return push_mpz(L, to_mpz_ext(L, 1) / arg2);
}

static int mpz_umn(lua_State * L) {
    return push_mpz(L, 0 - to_mpz_ext(L, 1));
}

static int mpz_power(lua_State * L) {
    int k = luaL_checkinteger(L, 2);
    if (k < 0) throw exception("argument #2 must be positive");
    return push_mpz(L, pow(to_mpz_ext(L, 1), k));
}

static int mk_mpz(lua_State * L) {
    mpz arg = to_mpz_ext(L, 1);
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
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, mpz_m, 0);

    SET_GLOBAL_FUN(mk_mpz,   "mpz");
    SET_GLOBAL_FUN(mpz_pred, "is_mpz");
}
}

void print(lean::mpz const & n) { std::cout << n << std::endl; }
