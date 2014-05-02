/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/thread.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpbq.h"

namespace lean {

const mpq numeric_traits<mpq>::pi_l((3373259426.0 + 273688.0 / (1<<21)) / (1<<30));
const mpq numeric_traits<mpq>::pi_n((3373259426.0 + 273688.0 / (1<<21)) / (1<<30));
const mpq numeric_traits<mpq>::pi_u((3373259426.0 + 273688.0 / (1<<21)) / (1<<30));

mpq & mpq::operator=(mpbq const & b) {
    *this = 2;
    power(*this, *this, b.get_k());
    inv();
    *this *= b.get_numerator();
    return *this;
}

int cmp(mpq const & a, mpz const & b) {
    if (a.is_integer()) {
        return mpz_cmp(mpq_numref(a.m_val), mpq::zval(b));
    } else {
        static LEAN_THREAD_LOCAL mpz tmp;
        mpz_mul(mpq::zval(tmp), mpq_denref(a.m_val), mpq::zval(b));
        return mpz_cmp(mpq_numref(a.m_val), mpq::zval(tmp));
    }
}

void mpq::floor() {
    if (is_integer())
        return;
    bool neg = is_neg();
    mpz_tdiv_q(mpq_numref(m_val), mpq_numref(m_val), mpq_denref(m_val));
    mpz_set_ui(mpq_denref(m_val), 1);
    if (neg)
        mpz_sub_ui(mpq_numref(m_val), mpq_numref(m_val), 1);
}

void mpq::ceil() {
    if (is_integer())
        return;
    bool pos = is_pos();
    mpz_tdiv_q(mpq_numref(m_val), mpq_numref(m_val), mpq_denref(m_val));
    mpz_set_ui(mpq_denref(m_val), 1);
    if (pos)
        mpz_add_ui(mpq_numref(m_val), mpq_numref(m_val), 1);
}

mpz floor(mpq const & a) {
    if (a.is_integer())
        return a.get_numerator();
    mpz r;
    mpz_tdiv_q(mpq::zval(r), mpq_numref(a.m_val), mpq_denref(a.m_val));
    if (a.is_neg())
        --r;
    return r;
}

mpz ceil(mpq const & a) {
    if (a.is_integer())
        return a.get_numerator();
    mpz r;
    mpz_tdiv_q(mpq::zval(r), mpq_numref(a.m_val), mpq_denref(a.m_val));
    if (a.is_pos())
        ++r;
    return r;
}

void power(mpq & a, mpq const & b, unsigned k) {
    mpz_pow_ui(mpq_numref(a.m_val), mpq_numref(b.m_val), k);
    mpz_pow_ui(mpq_denref(a.m_val), mpq_denref(b.m_val), k);
    mpq_canonicalize(a.m_val);
}

extern void display(std::ostream & out, __mpz_struct const * v);

std::ostream & operator<<(std::ostream & out, mpq const & v) {
    if (v.is_integer()) {
        display(out, mpq_numref(v.m_val));
    } else {
        display(out, mpq_numref(v.m_val));
        out << "/";
        display(out, mpq_denref(v.m_val));
    }
    return out;
}

void display_decimal(std::ostream & out, mpq const & a, unsigned prec) {
    mpz n1, d1, v1;
    numerator(n1, a);
    denominator(d1, a);
    if (a.is_neg()) {
        out << "-";
        n1.neg();
    }
    v1 = n1 / d1;
    out << v1;
    n1 = rem(n1, d1);
    if (n1.is_zero())
        return;
    out << ".";
    for (unsigned i = 0; i < prec; i++) {
        n1 *= 10;
        v1 = n1 / d1;
        lean_assert(v1 < 10);
        out << v1;
        n1 = rem(n1, d1);
        if (n1.is_zero())
            return;
    }
    out << "?";
}

static mpq g_zero;

mpq const & numeric_traits<mpq>::zero() {
    lean_assert(is_zero(g_zero));
    return g_zero;
}

serializer & operator<<(serializer & s, mpq const & n) {
    std::ostringstream out;
    out << n;
    s << out.str();
    return s;
}

mpq read_mpq(deserializer & d) {
    return mpq(d.read_string().c_str());
}

DECL_UDATA(mpq)

template<int idx>
static mpq const & to_mpq(lua_State * L) {
    static LEAN_THREAD_LOCAL mpq arg;
    switch (lua_type(L, idx)) {
    case LUA_TNUMBER:       arg = lua_tonumber(L, idx); return arg;
    case LUA_TSTRING:       arg = mpq(lua_tostring(L, idx)); return arg;
    case LUA_TUSERDATA:
        if (is_mpz(L, idx)) {
            arg = mpq(to_mpz(L, idx));
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
            return mpq(to_mpz(L, idx));
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
    return push_string(L, out.str().c_str());
}

static int mpq_eq(lua_State * L) {
    return push_boolean(L, to_mpq<1>(L) == to_mpq<2>(L));
}

static int mpq_lt(lua_State * L) {
    return push_boolean(L, to_mpq<1>(L) < to_mpq<2>(L));
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

static void mpq_migrate(lua_State * src, int i, lua_State * tgt) {
    push_mpq(tgt, to_mpq(src, i));
}

void open_mpq(lua_State * L) {
    luaL_newmetatable(L, mpq_mt);
    set_migrate_fn_field(L, -1, mpq_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, mpq_m, 0);

    SET_GLOBAL_FUN(mk_mpq,   "mpq");
    SET_GLOBAL_FUN(mpq_pred, "is_mpq");
}
}

void print(lean::mpq const & v) { std::cout << v << std::endl; }
