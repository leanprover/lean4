/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include <cstring>
#include "runtime/sstream.h"
#include "runtime/buffer.h"
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
    if (v < 0) w = -static_cast<uint64>(v);
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

mpz & mpz::operator+=(int u) { if (u >= 0) mpz_add_ui(m_val, m_val, u); else mpz_sub_ui(m_val, m_val, -static_cast<unsigned>(u)); return *this; }

mpz & mpz::operator-=(mpz const & o) { mpz_sub(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator-=(unsigned u) { mpz_sub_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator-=(int u) { if (u >= 0) mpz_sub_ui(m_val, m_val, u); else mpz_add_ui(m_val, m_val, -static_cast<unsigned>(u)); return *this; }

mpz & mpz::operator*=(mpz const & o) { mpz_mul(m_val, m_val, o.m_val); return *this; }

mpz & mpz::operator*=(unsigned u) { mpz_mul_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator*=(int u) { mpz_mul_si(m_val, m_val, u); return *this; }

mpz mpz::ediv(mpz const & n, mpz const & d) {
    mpz q;
    mpz_t r;
    mpz_init(r);
    /* (q,r) = (n/d, n%d) */
    mpz_tdiv_qr(q.m_val, r, n.m_val, d.m_val);
    /* if (r < 0) */
    if (mpz_sgn(r) < 0) {
        if (mpz_sgn(d.m_val) > 0) {
            /* q = q - 1. */
            mpz_sub_ui(q.m_val, q.m_val, 1);
        } else {
            /* q = q + 1. */
            mpz_add_ui(q.m_val, q.m_val, 1);
        }
    }
    mpz_clear(r);
    return q;
}

mpz mpz::emod(mpz const & n, mpz const & d) {
    mpz r;
    /* (q,r) = (n/d, n%d) */
    mpz_tdiv_r(r.m_val, n.m_val, d.m_val);
    /* if (r < 0) */
    if (mpz_sgn(r.m_val) < 0) {
        if (mpz_sgn(d.m_val) > 0) {
            /* r = r + d. */
            mpz_add(r.m_val, r.m_val, d.m_val);
        } else {
            /* r = r - d. */
            mpz_sub(r.m_val, r.m_val, d.m_val);
        }
    }
    return r;
}

mpz & mpz::operator/=(mpz const & o) { mpz_tdiv_q(m_val, m_val, o.m_val); return *this; }
mpz & mpz::operator/=(unsigned u) { mpz_tdiv_q_ui(m_val, m_val, u); return *this; }

mpz & mpz::operator%=(mpz const & o) { mpz_tdiv_r(m_val, m_val, o.m_val); return *this; }

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

uint8 mpz::mod8() const {
    mpz a;
    mpz_fdiv_r_2exp(a.m_val, m_val, 8);
    return static_cast<uint8>(a.get_unsigned_int());
}

uint16 mpz::mod16() const {
    mpz a;
    mpz_fdiv_r_2exp(a.m_val, m_val, 16);
    return static_cast<uint16>(a.get_unsigned_int());
}

uint32 mpz::mod32() const {
    mpz a;
    mpz_fdiv_r_2exp(a.m_val, m_val, 32);
    return static_cast<uint32>(a.get_unsigned_int());
}

uint64 mpz::mod64() const {
    mpz r;
    mpz_fdiv_r_2exp(r.m_val, m_val, 64);
    mpz l;
    mpz_fdiv_r_2exp(l.m_val, r.m_val, 32);
    mpz h;
    mpz_fdiv_q_2exp(h.m_val, r.m_val, 32);
    return (static_cast<uint64>(h.get_unsigned_int()) << 32) + static_cast<uint64>(l.get_unsigned_int());
}

int8 mpz::smod8() const {
    return static_cast<int8>(mod8());
}

int16 mpz::smod16() const {
    return static_cast<int16>(mod16());
}

int32 mpz::smod32() const {
    return static_cast<int32>(mod32());
}

int64 mpz::smod64() const {
    return static_cast<int64>(mod64());
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

static void *mpz_alloc(size_t size) {
#ifdef LEAN_SMALL_ALLOCATOR
    return alloc(size);
#else
    return malloc(size);
#endif
}

static void mpz_dealloc(void *ptr, size_t size) {
#ifdef LEAN_SMALL_ALLOCATOR
        dealloc(ptr, size);
#else
        free_sized(ptr, size);
#endif
}

void mpz::allocate(size_t s) {
    m_size   = s;
    m_digits = static_cast<mpn_digit*>(mpz_alloc(s * sizeof(mpn_digit)));
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
        m_digits[0] = -static_cast<unsigned>(v);
    } else {
        m_sign      = false;
        m_digits[0] = v;
    }
}

void mpz::init_uint64(uint64 v) {
    m_sign = false;
    if (v <= std::numeric_limits<unsigned>::max()) {
        allocate(1);
        m_digits[0] = v;
    } else {
        static_assert(sizeof(uint64) == 2 * sizeof(unsigned), "unsigned should be half the size of an uint64");
        allocate(2);
        m_digits[0] = static_cast<mpn_digit>(v);
        m_digits[1] = static_cast<mpn_digit>(v >> 8*sizeof(mpn_digit));
    }
}

void mpz::init_int64(int64 v) {
    if (v >= 0) {
        init_uint64(v);
    } else {
        init_uint64(-static_cast<uint64>(v));
        m_sign = true;
    }
}

void mpz::init_mpz(mpz const & v) {
    m_sign   = v.m_sign;
    m_size   = v.m_size;
    m_digits = static_cast<mpn_digit*>(mpz_alloc(m_size * sizeof(mpn_digit)));
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
    if (m_digits) {
        mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
    }
}

void swap(mpz & a, mpz & b) {
    std::swap(a.m_sign, b.m_sign);
    std::swap(a.m_size, b.m_size);
    std::swap(a.m_digits, b.m_digits);
}

int mpz::sgn() const {
    if (m_size == 1 && m_digits[0] == 0)
        return 0;
    else
        return m_sign ? -1 : 1;
}

bool mpz::is_int() const {
    if (m_sign) {
        return m_size == 1 && m_digits[0] <= -static_cast<unsigned>(std::numeric_limits<int>::min());
    } else {
        return m_size == 1 && m_digits[0] <= std::numeric_limits<int>::max();
    }
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
    lean_assert(is_int());
    if (m_sign) {
        return -static_cast<int>(m_digits[0]);
    } else {
        return m_digits[0];
    }
}

unsigned int mpz::get_unsigned_int() const {
    lean_assert(is_unsigned_int());
    return m_digits[0];
}

size_t mpz::get_size_t() const {
    lean_assert(is_size_t());
    if (sizeof(size_t) == 8) {
        if (m_size == 1)
            return m_digits[0];
        else
            return m_digits[0] + (static_cast<size_t>(m_digits[1]) << 8*sizeof(mpn_digit));
    } else {
        return m_digits[0];
    }
}

mpz & mpz::operator=(mpz const & v) {
    if (v.m_digits != m_digits) {
        if (v.m_size == m_size) {
            memcpy(m_digits, v.m_digits, m_size * sizeof(mpn_digit));
        } else {
            mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
            init_mpz(v);
        }
    }
    return *this;
}

mpz & mpz::operator=(char const * v) {
    mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
    init_str(v);
    return *this;
}

mpz & mpz::operator=(unsigned int v) {
    mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
    init_uint(v);
    return *this;
}

mpz & mpz::operator=(int v) {
    mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
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
            unsigned b1 = -static_cast<unsigned>(b);
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
        mpz_dealloc(m_digits, sizeof(mpn_digit)*m_size);
        allocate(sz);
    }
    memcpy(m_digits, digits, sizeof(mpn_digit)*sz);
}

typedef buffer<mpn_digit, 256> digit_buffer;

mpz & mpz::add(bool sign, size_t sz, mpn_digit const * digits) {
    digit_buffer tmp;
    if (m_sign == sign) {
        size_t new_sz = std::max(m_size, sz)+1;
        size_t real_sz;
        tmp.ensure_capacity(new_sz);
        mpn_add(m_digits, m_size,
                digits, sz,
                tmp.begin(), new_sz, &real_sz);
        lean_assert(real_sz <= new_sz);
        set(real_sz, tmp.begin());
    } else {
        mpn_digit borrow;
        int r = mpn_compare(m_digits, m_size,
                            digits, sz);
        if (r == 0) {
            operator=(0);
            return *this;
        } else if (r < 0) {
            size_t new_sz = sz;
            tmp.ensure_capacity(new_sz);
            mpn_sub(digits, sz,
                    m_digits, m_size,
                    tmp.begin(), &borrow);
            lean_assert(borrow==0);
            m_sign = sign;
            set(new_sz, tmp.begin());
        } else {
            // r > 0
            size_t new_sz = m_size;
            tmp.ensure_capacity(new_sz);
            mpn_sub(m_digits, m_size,
                    digits, sz,
                    tmp.begin(), &borrow);
            lean_assert(borrow == 0);
            set(new_sz, tmp.begin());
        }
    }
    return *this;
}

mpz & mpz::mul(bool sign, size_t sz, mpn_digit const * digits) {
    digit_buffer tmp;
    size_t new_sz = m_size + sz;
    tmp.ensure_capacity(new_sz);
    mpn_mul(m_digits, m_size,
            digits, sz,
            tmp.begin());
    set(new_sz, tmp.begin());
    m_sign = !is_zero() && m_sign != sign;
    return *this;
}

mpz & mpz::div(bool sign, size_t sz, mpn_digit const * digits) {
    /*
      +26 / +7 = +3, remainder is +5
      -26 / +7 = -3, remainder is -5
      +26 / -7 = -3, remainder is +5
      -26 / -7 = +3, remainder is -5
    */
    digit_buffer q1, r1;
    if (sz > m_size) {
        operator=(0);
        return *this;
    }
    size_t q_sz = m_size - sz + 1;
    size_t r_sz = sz;
    q1.ensure_capacity(q_sz);
    r1.ensure_capacity(r_sz);
    mpn_div(m_digits, m_size,
            digits, sz,
            q1.begin(), r1.begin());
    set(q_sz, q1.begin());
    m_sign = !is_zero() && m_sign != sign;
    return *this;
}

mpz & mpz::rem(size_t sz, mpn_digit const * digits) {
    /*
      +26 / +7 = +3, remainder is +5
      -26 / +7 = -3, remainder is -5
      +26 / -7 = -3, remainder is +5
      -26 / -7 = +3, remainder is -5
    */
    digit_buffer q1, r1;
    if (sz > m_size) {
        return *this;
    }
    size_t q_sz = m_size - sz + 1;
    size_t r_sz = sz;
    q1.ensure_capacity(q_sz);
    r1.ensure_capacity(r_sz);
    mpn_div(m_digits, m_size,
            digits, sz,
            q1.begin(), r1.begin());
    set(r_sz, r1.begin());
    m_sign = m_sign && !is_zero();
    return *this;
}

mpz & mpz::operator+=(mpz const & o) {
    return add(o.m_sign, o.m_size, o.m_digits);
}

mpz & mpz::operator+=(unsigned u) {
    return add(false, 1, &u);
}

mpz & mpz::operator+=(int u) {
    if (u < 0) {
        unsigned u1 = -static_cast<unsigned>(u);
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
        unsigned u1 = -static_cast<unsigned>(u);
        return add(false, 1, &u1);
    } else {
        unsigned u1 = u;
        return add(true, 1, &u1);
    }
}

mpz & mpz::operator*=(mpz const & o) {
    return mul(o.m_sign, o.m_size, o.m_digits);
}

mpz & mpz::operator*=(unsigned u) {
    return mul(false, 1, &u);
}

mpz & mpz::operator*=(int u) {
    if (u < 0) {
        unsigned u1 = -static_cast<unsigned>(u);
        return mul(true, 1, &u1);
    } else {
        unsigned u1 = u;
        return mul(false, 1, &u1);
    }
}

mpz & mpz::operator/=(mpz const & o) {
    return div(o.m_sign, o.m_size, o.m_digits);
}

mpz & mpz::operator/=(unsigned u) {
    return div(false, 1, &u);
}

mpz & mpz::operator%=(mpz const & o) {
    return rem(o.m_size, o.m_digits);
}

mpz mpz::ediv(mpz const & n, mpz const & d) {
    if (d.m_size > n.m_size) {
        if (n.is_neg()) {
            int64_t r = d.is_pos() ? -1 : 1;
            return mpz(r);
        } else {
            return mpz(0);
        }
    } else {
        digit_buffer q1, r1;
        size_t q_sz = n.m_size - d.m_size + 1;
        size_t r_sz = d.m_size;
        q1.ensure_capacity(q_sz);
        r1.ensure_capacity(r_sz);
        mpn_div(n.m_digits, n.m_size,
                d.m_digits, d.m_size,
                q1.begin(), r1.begin());
        mpz q;
        q.set(q_sz, q1.begin());
        q.m_sign = !q.is_zero() && n.m_sign != d.m_sign;
        mpz r;
        r.set(r_sz, r1.begin());
        r.m_sign = n.m_sign && !r.is_zero();
        if (r.is_neg()) {
            if (d.is_pos()) {
                q -= 1;
            } else {
                q += 1;
            }
        }
        return q;
    }
}

mpz mpz::emod(mpz const & n, mpz const & d) {
    mpz r(n);
    r.rem(d.m_size, d.m_digits);
    if (r.is_neg()) {
        if (d.is_pos()) {
            r += d;
        } else {
            r -= d;
        }
    }
    return r;
}

mpz mpz::pow(unsigned int p) const {
    unsigned mask = 1;
    mpz power(*this);
    mpz result(1);
    while (mask <= p) {
        if (mask & p)
            result *= power;
        power *= power;
        mask = mask << 1;
    }
    return result;
}

static unsigned log2_uint(unsigned v) {
    unsigned r = 0;
    if (v & 0xFFFF0000) {
        v >>= 16;
        r |=  16;
    }
    if (v & 0xFF00) {
        v >>= 8;
        r |=  8;
    }
    if (v & 0xF0) {
        v >>= 4;
        r |=  4;
    }
    if (v & 0xC) {
        v >>= 2;
        r |=  2;
    }
    if (v & 0x2) {
        v >>= 1;
        r |=  1;
    }
    return r;
}

size_t mpz::log2() const {
    return (m_size - 1)*sizeof(mpn_digit)*8 + log2_uint(m_digits[m_size - 1]);
}

mpz & mpz::operator&=(mpz const & o) {
    digit_buffer r;
    size_t sz = std::max(m_size, o.m_size);
    r.ensure_capacity(sz);
    for (size_t i = 0; i < sz; i++) {
        mpn_digit u_i = (i < m_size)   ? m_digits[i]   : 0;
        mpn_digit v_i = (i < o.m_size) ? o.m_digits[i] : 0;
        r.push_back(u_i & v_i);
    }
    set(sz, r.begin());
    return *this;
}

mpz & mpz::operator|=(mpz const & o) {
    digit_buffer r;
    size_t sz = std::max(m_size, o.m_size);
    r.ensure_capacity(sz);
    for (size_t i = 0; i < sz; i++) {
        mpn_digit u_i = (i < m_size)   ? m_digits[i]   : 0;
        mpn_digit v_i = (i < o.m_size) ? o.m_digits[i] : 0;
        r.push_back(u_i | v_i);
    }
    set(sz, r.begin());
    return *this;
}

mpz & mpz::operator^=(mpz const & o) {
    digit_buffer r;
    size_t sz = std::max(m_size, o.m_size);
    r.ensure_capacity(sz);
    for (size_t i = 0; i < sz; i++) {
        mpn_digit u_i = (i < m_size)   ? m_digits[i]   : 0;
        mpn_digit v_i = (i < o.m_size) ? o.m_digits[i] : 0;
        r.push_back(u_i ^ v_i);
    }
    set(sz, r.begin());
    return *this;
}

void mul2k(mpz & a, mpz const & b, unsigned k) {
    lean_assert(!b.m_sign);
    if (k == 0 || b.is_zero()) {
        a = b;
        return;
    }
    unsigned word_shift  = k / (8 * sizeof(mpn_digit));
    unsigned bit_shift   = k % (8 * sizeof(mpn_digit));
    size_t   old_sz      = b.m_size;
    size_t   new_sz      = old_sz + word_shift + 1;
    digit_buffer ds;
    ds.ensure_capacity(new_sz);
    for (size_t i = 0; i < word_shift; i++) {
        ds.push_back(0);
    }
    for (size_t i = 0; i < old_sz; i++) {
        ds.push_back(b.m_digits[i]);
    }
    ds.push_back(0);
    if (bit_shift > 0) {
        unsigned comp_shift = (8 * sizeof(mpn_digit)) - bit_shift;
        mpn_digit prev = 0;
        for (size_t i = word_shift; i < new_sz; i++) {
            mpn_digit new_prev = (ds[i] >> comp_shift);
            ds[i] <<= bit_shift;
            ds[i] |= prev;
            prev = new_prev;
        }
    }
    a.m_sign = false;
    a.set(new_sz, ds.begin());
}

void div2k(mpz & a, mpz const & b, unsigned k) {
    lean_assert(!b.m_sign);
    if (k == 0 || b.is_zero()) {
        a = b;
        return;
    }
    unsigned digit_shift = k / (8 * sizeof(mpn_digit));
    if (digit_shift >= b.m_size) {
        a = 0;
        return;
    }
    size_t sz           = b.m_size;
    size_t new_sz       = sz - digit_shift;
    unsigned bit_shift  = k % (8 * sizeof(mpn_digit));
    unsigned comp_shift = (8 * sizeof(mpn_digit)) - bit_shift;
    digit_buffer ds;
    ds.append(b.m_size, b.m_digits);
    if (new_sz < sz) {
        size_t i       = 0;
        size_t j       = digit_shift;
        if (bit_shift != 0) {
            for (; i < new_sz - 1; i++, j++) {
                ds[i] = ds[j];
                ds[i] >>= bit_shift;
                ds[i] |= (ds[j+1] << comp_shift);
            }
            ds[i] = ds[j];
            ds[i] >>= bit_shift;
        }
        else {
            for (; i < new_sz; i++, j++) {
                ds[i] = ds[j];
            }
        }
    }
    else {
        size_t i = 0;
        for (; i < new_sz - 1; i++) {
            ds[i] >>= bit_shift;
            ds[i] |= (ds[i+1] << comp_shift);
        }
        ds[i] >>= bit_shift;
    }
    a.m_sign = false;
    a.set(new_sz, ds.begin());
}

uint8 mpz::mod8() const {
    uint8 ret = static_cast<uint8>(m_digits[0] & 0xFFu);
    if (m_sign) {
        ret = -ret;
    }
    return ret;
}

uint16 mpz::mod16() const {
    uint16 ret = static_cast<uint16>(m_digits[0] & 0xFFFFu);
    if (m_sign) {
        ret = -ret;
    }
    return ret;
}

uint32 mpz::mod32() const {
    uint32 ret = static_cast<uint32>(m_digits[0]);
    if (m_sign) {
        ret = -ret;
    }
    return ret;
}

uint64 mpz::mod64() const {
    uint64 ret;
    if (m_size == 1) {
        ret = m_digits[0];
    }
    else {
        ret = m_digits[0] + (static_cast<uint64>(m_digits[1]) << 8*sizeof(mpn_digit));
    }
    if (m_sign) {
        ret = -ret;
    }
    return ret;
}

int8 mpz::smod8() const {
    return static_cast<int8>(mod8());
}

int16 mpz::smod16() const {
    return static_cast<int16>(mod16());
}

int32 mpz::smod32() const {
    return static_cast<int32>(mod32());
}

int64 mpz::smod64() const {
    return static_cast<int64>(mod64());
}

void power(mpz & a, mpz const & b, unsigned k) {
    a = b;
    a.pow(k);
}

void gcd(mpz & g, mpz const & a, mpz const & b) {
    mpz tmp1(a);
    mpz tmp2(b);
    mpz aux;
    tmp1.abs();
    tmp2.abs();
    if (tmp1 < tmp2)
        swap(tmp1, tmp2);

    if (tmp2.is_zero()) {
        swap(g, tmp1);
    } else {
        while (true) {
            aux = rem(tmp1, tmp2);
            if (aux.is_zero()) {
                swap(g, tmp2);
                break;
            }
            swap(tmp1, tmp2);
            swap(tmp2, aux);
        }
    }
}

std::ostream & operator<<(std::ostream & out, mpz const & v) {
    if (v.m_sign)
        out << "-";
    buffer<char, 1024> tmp;
    tmp.resize(11*v.m_size, 0);
    out << mpn_to_string(v.m_digits, v.m_size, tmp.begin(), tmp.size());
    return out;
}
#endif


std::string mpz::to_string() const {
    std::ostringstream out;
    out << *this;
    return out.str();
}
}

void print(lean::mpz const & n) { std::cout << n << std::endl; }
