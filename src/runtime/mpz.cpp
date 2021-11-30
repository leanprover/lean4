/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include <cstring>
#include "runtime/sstream.h"
#include "runtime/alloc.h"
#include "runtime/thread.h"
#include "runtime/mpz.h"
#include "runtime/debug.h"

namespace lean {
/***** GMP VERSION ******/
#ifdef LEAN_USE_GMP
mpz::mpz() {
    mpz_init(m_val);
}

mpz::mpz(mpz_t v) {
    mpz_init(m_val);
    mpz_set(m_val, v);
}

mpz::mpz(char const * v) {
    mpz_init_set_str(m_val, const_cast<char*>(v), 10);
}

mpz::mpz(unsigned int v) {
    mpz_init_set_ui(m_val, v);
}

mpz::mpz(int v) {
    mpz_init_set_si(m_val, v);
}

mpz::mpz(uint64 v):
    mpz(static_cast<unsigned>(v)) {
    mpz tmp(static_cast<unsigned>(v >> 32));
    mpz_mul_2exp(tmp.m_val, tmp.m_val, 32);
    mpz_add(m_val, m_val, tmp.m_val);
}

mpz::mpz(int64 v) {
    uint64 w;
    if (v < 0) w = -v;
    else w = v;
    mpz_init_set_ui(m_val, static_cast<unsigned>(w));
    mpz tmp(static_cast<unsigned>(w >> 32));
    mpz_mul_2exp(tmp.m_val, tmp.m_val, 32);
    mpz_add(m_val, m_val, tmp.m_val);
    if (v < 0)
        mpz_neg(m_val, m_val);
}

mpz::mpz(mpz const & s) {
    mpz_init_set(m_val, s.m_val);
}

mpz::mpz(mpz && s):mpz() {
    mpz_swap(m_val, s.m_val);
}

mpz::~mpz() {
    mpz_clear(m_val);
}

void mpz::set(mpz_t r) const {
    mpz_set(r, m_val);
}

void swap(mpz & a, mpz & b) {
    mpz_swap(a.m_val, b.m_val);
}

int mpz::sgn() const {
    return mpz_sgn(m_val);
}

bool mpz::is_int() const {
    return mpz_fits_sint_p(m_val) != 0;
}

bool mpz::is_unsigned_int() const {
    return mpz_fits_uint_p(m_val) != 0;
}

bool mpz::is_size_t() const {
    // GMP only features `fits` functions up to `unsigned long`, which is smaller than `size_t` on Windows.
    // So we directly count the number of mpz words instead.
    static_assert(sizeof(size_t) == sizeof(mp_limb_t), "GMP word size should be equal to system word size");
    return is_nonneg() && mpz_size(m_val) <= 1;
}

int mpz::get_int() const {
    lean_assert(is_int());
    return static_cast<int>(mpz_get_si(m_val));
}

unsigned int mpz::get_unsigned_int() const {
    lean_assert(is_unsigned_int());
    return static_cast<unsigned>(mpz_get_ui(m_val));
}

size_t mpz::get_size_t() const {
    // GMP only features accessors up to `unsigned long`, which is smaller than `size_t` on Windows.
    // So we directly access the lowest mpz word instead.
    static_assert(sizeof(size_t) == sizeof(mp_limb_t), "GMP word size should be equal system word size");
    // NOTE: mpz_getlimbn returns 0 if the index is out of range (i.e. `m_val == 0`)
    return static_cast<size_t>(mpz_getlimbn(m_val, 0));
}

mpz & mpz::operator=(mpz const & v) {
    mpz_set(m_val, v.m_val); return *this;
}

mpz & mpz::operator=(char const * v) {
    mpz_set_str(m_val, v, 10); return *this;
}

mpz & mpz::operator=(unsigned int v) {
    mpz_set_ui(m_val, v); return *this;
}

mpz & mpz::operator=(int v) {
    mpz_set_si(m_val, v); return *this;
}

int cmp(mpz const & a, mpz const & b) {
    return mpz_cmp(a.m_val, b.m_val);
}

int cmp(mpz const & a, unsigned b) {
    return mpz_cmp_ui(a.m_val, b);
}

int cmp(mpz const & a, int b) {
    return mpz_cmp_si(a.m_val, b);
}

mpz & mpz::operator+=(mpz const & o) { mpz_add(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator+=(unsigned u) { mpz_add_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator+=(int u) { if (u >= 0) mpz_add_ui(m_val, m_val, u); else mpz_sub_ui(m_val, m_val, -u); return *this; }

mpz & mpz::operator-=(mpz const & o) { mpz_sub(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator-=(unsigned u) { mpz_sub_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator-=(int u) { if (u >= 0) mpz_sub_ui(m_val, m_val, u); else mpz_add_ui(m_val, m_val, -u); return *this; }

mpz & mpz::operator*=(mpz const & o) { mpz_mul(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator*=(unsigned u) { mpz_mul_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator*=(int u) { mpz_mul_si(m_val, m_val, u); return *this; }

mpz & mpz::operator/=(mpz const & o) { mpz_tdiv_q(m_val, m_val, o.m_val); return *this; }
mpz & mpz::operator/=(unsigned u) { mpz_tdiv_q_ui(m_val, m_val, u); return *this; }

mpz rem(mpz const & a, mpz const & b) { mpz r; mpz_tdiv_r(r.m_val, a.m_val, b.m_val); return r; }

mpz mpz::pow(unsigned int exp) const {
    mpz r;
    mpz_pow_ui(r.m_val, m_val, exp);
    return r;
}

size_t mpz::log2() const {
    if (is_nonpos())
        return 0;
    size_t r = mpz_sizeinbase(m_val, 2);
    lean_assert(r > 0);
    return r - 1;
}

mpz operator%(mpz const & a, mpz const & b) {
    return rem(a, b);
}

mpz & mpz::operator&=(mpz const & o) {
    mpz_and(m_val, m_val, o.m_val);
    return *this;
}

mpz & mpz::operator|=(mpz const & o) {
    mpz_ior(m_val, m_val, o.m_val);
    return *this;
}

mpz & mpz::operator^=(mpz const & o) {
    mpz_xor(m_val, m_val, o.m_val);
    return *this;
}

void mul2k(mpz & a, mpz const & b, unsigned k) {
    mpz_mul_2exp(a.m_val, b.m_val, k);
}

void div2k(mpz & a, mpz const & b, unsigned k) {
    mpz_tdiv_q_2exp(a.m_val, b.m_val, k);
}

void mod2k(mpz & a, mpz const & b, unsigned k) {
    mpz_tdiv_r_2exp(a.m_val, b.m_val, k);
}

void power(mpz & a, mpz const & b, unsigned k) {
    mpz_pow_ui(a.m_val, b.m_val, k);
}

void gcd(mpz & g, mpz const & a, mpz const & b) {
    mpz_gcd(g.m_val, a.m_val, b.m_val);
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

#else
/***** NON GMP VERSION ******/

void mpz::allocate(size_t s) {
    m_size   = s;
    m_digits = static_cast<mpn_digit*>(alloc(s * sizeof(mpn_digit)));
}

void mpz::init() {
    allocate(1);
    m_sign      = false;
    m_digits[0] = 0;
}

void mpz::init_str(char const * v) {
    init();
    char const * str = v;
    bool sign = false;
    while (str[0] == ' ') ++str;
    if (str[0] == '-')
        sign = true;
    while (str[0]) {
        if ('0' <= str[0] && str[0] <= '9') {
            operator*=(10);
            operator+=(static_cast<unsigned>(str[0] - '0'));
        }
        ++str;
    }
    if (sign)
        neg();
}

void mpz::init_uint(unsigned int v) {
    allocate(1);
    m_sign   = false;
    m_digits[0] = v;
}

void mpz::init_int(int v) {
    allocate(1);
    if (v < 0) {
        m_sign      = true;
        m_digits[0] = -v;
    } else {
        m_sign      = false;
        m_digits[0] = v;
    }
}

void mpz::init_uint64(uint64 v) {
    if (v <= std::numeric_limits<unsigned>::max()) {
        allocate(1);
        m_sign      = false;
        m_digits[0] = v;
    } else {
        allocate(2);
        m_sign = false;
        (reinterpret_cast<uint64*>(m_digits))[0] = v;
    }
}

void mpz::init_int64(int64 v) {
    // TODO
    lean_unreachable();
}

void mpz::init_mpz(mpz const & v) {
    m_sign   = v.m_sign;
    m_size   = v.m_size;
    m_digits = static_cast<mpn_digit*>(alloc(m_size * sizeof(mpn_digit)));
    memcpy(m_digits, v.m_digits, m_size * sizeof(mpn_digit));
}

mpz::mpz() {
    init();
}

mpz::mpz(char const * v) {
    init_str(v);
}

mpz::mpz(unsigned int v) {
    init_uint(v);
}

mpz::mpz(int v) {
    init_int(v);
}

mpz::mpz(uint64 v) {
    init_uint64(v);
}

mpz::mpz(int64 v) {
    init_int64(v);
}

mpz::mpz(mpz const & s) {
    init_mpz(s);
}

mpz::mpz(mpz && s):
    m_sign(s.m_sign),
    m_size(s.m_size),
    m_digits(s.m_digits) {
    s.m_digits = nullptr;
}

mpz::~mpz() {
    if (m_digits)
        dealloc(m_digits, sizeof(mpn_digit)*m_size);
}

void swap(mpz & a, mpz & b) {
    std::swap(a.m_sign, b.m_sign);
    std::swap(a.m_size, b.m_size);
    std::swap(a.m_digits, b.m_digits);
}

int mpz::sgn() const {
    if (m_size > 1) {
        return m_sign ? -1 : 1;
    } else {
        if (m_digits[0] == 0)
            return 0;
        else
            return m_sign ? -1 : 1;
    }
}

bool mpz::is_int() const {
    // TODO
    lean_unreachable();
}

bool mpz::is_unsigned_int() const {
    return m_size == 1 && !m_sign;
}

bool mpz::is_size_t() const {
    if (sizeof(size_t) == 8) {
        return m_size <= 2 && !m_sign;
    } else {
        return m_size == 1 && !m_sign;
    }
}

int mpz::get_int() const {
    // TODO
    lean_unreachable();
}

unsigned int mpz::get_unsigned_int() const {
    // TODO
    lean_unreachable();
}

size_t mpz::get_size_t() const {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator=(mpz const & v) {
    dealloc(m_digits, sizeof(mpn_digit)*m_size);
    init_mpz(v);
    return *this;
}

mpz & mpz::operator=(char const * v) {
    dealloc(m_digits, sizeof(mpn_digit)*m_size);
    init_str(v);
    return *this;
}

mpz & mpz::operator=(unsigned int v) {
    dealloc(m_digits, sizeof(mpn_digit)*m_size);
    init_uint(v);
    return *this;
}

mpz & mpz::operator=(int v) {
    dealloc(m_digits, sizeof(mpn_digit)*m_size);
    init_int(v);
    return *this;
}

int cmp(mpz const & a, mpz const & b) {
    if (a.m_sign) {
        if (b.m_sign) {
            return mpn_compare(b.m_digits, b.m_size, a.m_digits, a.m_size);
        } else {
            return -1; // `a` is negative and `b` is nonnegative
        }
    } else {
        if (b.m_sign) {
            return 1; // `a` is nonnegative and `b` is negative
        } else {
            return mpn_compare(a.m_digits, a.m_size, b.m_digits, b.m_size);
        }
    }
}

int cmp(mpz const & a, unsigned b) {
    if (a.m_sign) {
        return -1;
    } else {
        return mpn_compare(a.m_digits, a.m_size, &b, 1);
    }
}

int cmp(mpz const & a, int b) {
    if (a.m_sign) {
        if (b < 0) {
            unsigned b1 = -b;
            return mpn_compare(&b1, 1, a.m_digits, a.m_size);
        } else {
            return -1;
        }
    } else {
        if (b < 0) {
            return 1;
        } else {
            unsigned b1 = b;
            return mpn_compare(a.m_digits, a.m_size, &b1, 1);
        }
    }
}

void mpz::set(size_t sz, mpn_digit const * digits) {
    while (sz > 1 && digits[sz - 1] == 0)
        sz--;
    if (sz != m_size) {
        dealloc(m_digits, sizeof(mpn_digit)*m_size);
        allocate(sz);
    }
    memcpy(m_digits, digits, sizeof(mpn_digit)*sz);
}

mpz & mpz::add(bool sign, size_t sz, mpn_digit const * digits) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator+=(mpz const & o) {
    return add(o.m_sign, o.m_size, o.m_digits);
}

mpz & mpz::operator+=(unsigned u) {
    return add(false, 1, &u);
}

mpz & mpz::operator+=(int u) {
    if (u < 0) {
        unsigned u1 = -u;
        return add(true, 1, &u1);
    } else {
        unsigned u1 = u;
        return add(false, 1, &u1);
    }
}

mpz & mpz::operator-=(mpz const & o) {
    return add(!o.m_sign, o.m_size, o.m_digits);
}

mpz & mpz::operator-=(unsigned u) {
    return add(true, 1, &u);
}

mpz & mpz::operator-=(int u) {
    if (u < 0) {
        unsigned u1 = -u;
        return add(false, 1, &u1);
    } else {
        unsigned u1 = u;
        return add(true, 1, &u1);
    }
}

mpz & mpz::operator*=(mpz const & o) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator*=(unsigned u) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator*=(int u) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator/=(mpz const & o) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator/=(unsigned u) {
    // TODO
    lean_unreachable();
}

mpz rem(mpz const & a, mpz const & b) {
    // TODO
    lean_unreachable();
}

mpz mpz::pow(unsigned int p) const {
    unsigned mask = 1;
    mpz power(p);
    mpz result(1);
    while (mask <= p) {
        if (mask & p)
            result *= power;
        power *= power;
        mask = mask << 1;
    }
    return result;
}

size_t mpz::log2() const {
    // TODO
    lean_unreachable();
}

mpz operator%(mpz const & a, mpz const & b) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator&=(mpz const & o) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator|=(mpz const & o) {
    // TODO
    lean_unreachable();
}

mpz & mpz::operator^=(mpz const & o) {
    // TODO
    lean_unreachable();
}

void mul2k(mpz & a, mpz const & b, unsigned k) {
    // TODO
    lean_unreachable();
}

void div2k(mpz & a, mpz const & b, unsigned k) {
    // TODO
    lean_unreachable();
}

void mod2k(mpz & a, mpz const & b, unsigned k) {
    // TODO
    lean_unreachable();
}

void power(mpz & a, mpz const & b, unsigned k) {
    a = b;
    a.pow(k);
}

void gcd(mpz & g, mpz const & a, mpz const & b) {
    // TODO
    lean_unreachable();
}

std::ostream & operator<<(std::ostream & out, mpz const & v) {
    // TODO
    lean_unreachable();
}
#endif


std::string mpz::to_string() const {
    std::ostringstream out;
    out << *this;
    return out.str();
}
}

void print(lean::mpz const & n) { std::cout << n << std::endl; }
