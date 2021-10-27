/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstddef>
#include <gmp.h>
#include <string>
#include <iostream>
#include <limits>
#include <lean/lean.h>
#include "runtime/int64.h"
#include "runtime/debug.h"

namespace lean {

/** \brief Wrapper for GMP integers */
class mpz {
    friend class object_compactor;
    friend class compacted_region;
    mpz_t m_val;
    mpz(__mpz_struct const * v) { mpz_init_set(m_val, v); }
public:
    mpz() { mpz_init(m_val); }
    explicit mpz(mpz_t v) { mpz_init(m_val); mpz_set(m_val, v); }
    explicit mpz(char const * v) { mpz_init_set_str(m_val, const_cast<char*>(v), 10); }
    explicit mpz(unsigned int v) { mpz_init_set_ui(m_val, v); }
    explicit mpz(int v) { mpz_init_set_si(m_val, v); }
    explicit mpz(uint64 v);
    explicit mpz(int64 v);
    static mpz of_size_t(size_t v) {
        if (sizeof(size_t) == sizeof(uint64)) // NOLINT
            return mpz((uint64) v); // NOLINT
        else
            return mpz((unsigned) v); // NOLINT
    }
    mpz(mpz const & s) { mpz_init_set(m_val, s.m_val); }
    mpz(mpz && s):mpz() { mpz_swap(m_val, s.m_val); }
    ~mpz() { mpz_clear(m_val); }

    void set(mpz_t r) const { mpz_set(r, m_val); }

    friend void swap(mpz & a, mpz & b) { mpz_swap(a.m_val, b.m_val); }

    unsigned hash() const { return static_cast<unsigned>(mpz_get_si(m_val)); }

    int sgn() const { return mpz_sgn(m_val); }
    friend int sgn(mpz const & a) { return a.sgn(); }
    bool is_pos() const { return sgn() > 0; }
    bool is_neg() const { return sgn() < 0; }
    bool is_zero() const { return sgn() == 0; }
    bool is_nonpos() const { return !is_pos(); }
    bool is_nonneg() const { return !is_neg(); }

    void neg() { mpz_neg(m_val, m_val); }
    friend mpz neg(mpz a) { a.neg(); return a; }

    void abs() { mpz_abs(m_val, m_val); }
    friend mpz abs(mpz a) { a.abs(); return a; }

    bool is_int() const { return mpz_fits_sint_p(m_val) != 0; }
    bool is_unsigned_int() const { return mpz_fits_uint_p(m_val) != 0; }
    bool is_long_int() const { return mpz_fits_slong_p(m_val) != 0; }
    bool is_unsigned_long_int() const { return mpz_fits_ulong_p(m_val) != 0; }
    bool is_size_t() const {
        // GMP only features `fits` functions up to `unsigned long`, which is smaller than `size_t` on Windows.
        // So we directly count the number of mpz words instead.
        static_assert(sizeof(size_t) == sizeof(mp_limb_t), "GMP word size should be equal to system word size");
        return is_nonneg() && mpz_size(m_val) <= 1;
    }

    long int get_long_int() const { lean_assert(is_long_int()); return mpz_get_si(m_val); }
    int get_int() const { lean_assert(is_int()); return static_cast<int>(get_long_int()); }
    unsigned long int get_unsigned_long_int() const { lean_assert(is_unsigned_long_int()); return mpz_get_ui(m_val); }
    unsigned int get_unsigned_int() const { lean_assert(is_unsigned_int()); return static_cast<unsigned>(get_unsigned_long_int()); }
    size_t get_size_t() const;

    mpz & operator=(mpz const & v) { mpz_set(m_val, v.m_val); return *this; }
    mpz & operator=(mpz && v) { swap(*this, v); return *this; }
    mpz & operator=(char const * v) { mpz_set_str(m_val, v, 10); return *this; }
    mpz & operator=(unsigned int v) { mpz_set_ui(m_val, v); return *this; }
    mpz & operator=(int v) { mpz_set_si(m_val, v); return *this; }

    friend int cmp(mpz const & a, mpz const & b) { return mpz_cmp(a.m_val, b.m_val); }
    friend int cmp(mpz const & a, unsigned b) { return mpz_cmp_ui(a.m_val, b); }
    friend int cmp(mpz const & a, unsigned long b) { return mpz_cmp_ui(a.m_val, b); }
    friend int cmp(mpz const & a, int b) { return mpz_cmp_si(a.m_val, b); }

    friend bool operator<(mpz const & a, mpz const & b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, unsigned b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, unsigned long b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, int b) { return cmp(a, b) < 0; }
    friend bool operator<(unsigned a, mpz const & b) { return cmp(b, a) > 0; }
    friend bool operator<(int a, mpz const & b) { return cmp(b, a) > 0; }

    friend bool operator>(mpz const & a, mpz const & b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, unsigned b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, unsigned long b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, int b) { return cmp(a, b) > 0; }
    friend bool operator>(unsigned a, mpz const & b) { return cmp(b, a) < 0; }
    friend bool operator>(int a, mpz const & b) { return cmp(b, a) < 0; }

    friend bool operator<=(mpz const & a, mpz const & b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, unsigned b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, unsigned long b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, int b) { return cmp(a, b) <= 0; }
    friend bool operator<=(unsigned a, mpz const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(int a, mpz const & b) { return cmp(b, a) >= 0; }

    friend bool operator>=(mpz const & a, mpz const & b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, unsigned b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, unsigned long b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, int b) { return cmp(a, b) >= 0; }
    friend bool operator>=(unsigned a, mpz const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(int a, mpz const & b) { return cmp(b, a) <= 0; }

    friend bool operator==(mpz const & a, mpz const & b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, unsigned b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, unsigned long b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, int b) { return cmp(a, b) == 0; }
    friend bool operator==(unsigned a, mpz const & b) { return cmp(b, a) == 0; }
    friend bool operator==(int a, mpz const & b) { return cmp(b, a) == 0; }

    friend bool operator!=(mpz const & a, mpz const & b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, unsigned b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, unsigned long b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, int b) { return cmp(a, b) != 0; }
    friend bool operator!=(unsigned a, mpz const & b) { return cmp(b, a) != 0; }
    friend bool operator!=(int a, mpz const & b) { return cmp(b, a) != 0; }

    mpz & operator+=(mpz const & o) { mpz_add(m_val, m_val, o.m_val); return *this; }
    mpz & operator+=(unsigned u) { mpz_add_ui(m_val, m_val, u); return *this; }
    mpz & operator+=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this += mpz(u) : *this += static_cast<unsigned>(u); }
    mpz & operator+=(int u) { if (u >= 0) mpz_add_ui(m_val, m_val, u); else mpz_sub_ui(m_val, m_val, -u); return *this; }

    mpz & operator-=(mpz const & o) { mpz_sub(m_val, m_val, o.m_val); return *this; }
    mpz & operator-=(unsigned u) { mpz_sub_ui(m_val, m_val, u); return *this; }
    mpz & operator-=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this -= mpz(u) : *this -= static_cast<unsigned>(u); }
    mpz & operator-=(int u) { if (u >= 0) mpz_sub_ui(m_val, m_val, u); else mpz_add_ui(m_val, m_val, -u); return *this; }

    mpz & operator*=(mpz const & o) { mpz_mul(m_val, m_val, o.m_val); return *this; }
    mpz & operator*=(unsigned u) { mpz_mul_ui(m_val, m_val, u); return *this; }
    mpz & operator*=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this *= mpz(u) : *this *= static_cast<unsigned>(u); }
    mpz & operator*=(int u) { mpz_mul_si(m_val, m_val, u); return *this; }

    mpz & operator/=(mpz const & o) { mpz_tdiv_q(m_val, m_val, o.m_val); return *this; }
    mpz & operator/=(unsigned u) { mpz_tdiv_q_ui(m_val, m_val, u); return *this; }
    mpz & operator/=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this /= mpz(u) : *this /= static_cast<unsigned>(u); }
    mpz & operator/=(int u) { return operator/=(mpz(u)); } // TODO(Leo): improve

    friend mpz rem(mpz const & a, mpz const & b) { mpz r; mpz_tdiv_r(r.m_val, a.m_val, b.m_val); return r; }
    mpz & operator%=(mpz const & o) { mpz r(*this % o); mpz_swap(m_val, r.m_val); return *this; }
    mpz pow(unsigned int exp) const { mpz r; mpz_pow_ui(r.m_val, m_val, exp); return r; }

    friend mpz operator+(mpz a, mpz const & b) { return a += b; }
    friend mpz operator+(mpz a, unsigned b)  { return a += b; }
    friend mpz operator+(mpz a, uint64 b)  { return a += b; }
    friend mpz operator+(mpz a, int b)  { return a += b; }
    friend mpz operator+(unsigned a, mpz b) { return b += a; }
    friend mpz operator+(uint64 a, mpz b) { return b += a; }
    friend mpz operator+(int a, mpz b) { return b += a; }

    friend mpz operator-(mpz a, mpz const & b) { return a -= b; }
    friend mpz operator-(mpz a, unsigned b) { return a -= b; }
    friend mpz operator-(mpz a, uint64 b) { return a -= b; }
    friend mpz operator-(mpz a, int b) { return a -= b; }
    friend mpz operator-(unsigned a, mpz b) { b.neg(); return b += a; }
    friend mpz operator-(uint64 a, mpz b) { b.neg(); return b += a; }
    friend mpz operator-(int a, mpz b) { b.neg(); return b += a; }

    friend mpz operator*(mpz a, mpz const & b) { return a *= b; }
    friend mpz operator*(mpz a, unsigned b) { return a *= b; }
    friend mpz operator*(mpz a, uint64 b) { return a *= b; }
    friend mpz operator*(mpz a, int b) { return a *= b; }
    friend mpz operator*(unsigned a, mpz b) { return b *= a; }
    friend mpz operator*(uint64 a, mpz b) { return b *= a; }
    friend mpz operator*(int a, mpz b) { return b *= a; }

    friend mpz operator/(mpz a, mpz const & b) { return a /= b; }
    friend mpz operator/(mpz a, unsigned b) { return a /= b; }
    friend mpz operator/(mpz a, uint64 b) { return a /= b; }
    friend mpz operator/(mpz a, int b) { return a /= b; }
    friend mpz operator/(unsigned a, mpz const & b) { mpz r(a); return r /= b; }
    friend mpz operator/(uint64 a, mpz const & b) { mpz r(a); return r /= b; }
    friend mpz operator/(int a, mpz const & b) { mpz r(a); return r /= b; }

    friend mpz operator%(mpz const & a, mpz const & b);

    mpz & operator&=(mpz const & o) { mpz_and(m_val, m_val, o.m_val); return *this; }
    mpz & operator|=(mpz const & o) { mpz_ior(m_val, m_val, o.m_val); return *this; }
    mpz & operator^=(mpz const & o) { mpz_xor(m_val, m_val, o.m_val); return *this; }

    friend mpz operator&(mpz a, mpz const & b) { return a &= b; }
    friend mpz operator|(mpz a, mpz const & b) { return a |= b; }
    friend mpz operator^(mpz a, mpz const & b) { return a ^= b; }

    // a <- b * 2^k
    friend void mul2k(mpz & a, mpz const & b, unsigned k) { mpz_mul_2exp(a.m_val, b.m_val, k); }
    // a <- b / 2^k
    friend void div2k(mpz & a, mpz const & b, unsigned k) { mpz_tdiv_q_2exp(a.m_val, b.m_val, k); }
    // a <- b % 2^k
    friend void mod2k(mpz & a, mpz const & b, unsigned k) { mpz_tdiv_r_2exp(a.m_val, b.m_val, k); }

    /**
       \brief Return the position of the most significant bit.
       Return 0 if the number is negative
    */
    size_t log2() const;

    friend void power(mpz & a, mpz const & b, unsigned k) { mpz_pow_ui(a.m_val, b.m_val, k); }
    friend void _power(mpz & a, mpz const & b, unsigned k) { power(a, b, k); }
    friend mpz pow(mpz a, unsigned k) { power(a, a, k); return a; }

    friend void gcd(mpz & g, mpz const & a, mpz const & b) { mpz_gcd(g.m_val, a.m_val, b.m_val); }
    friend mpz gcd(mpz const & a, mpz const & b) { mpz r; gcd(r, a, b); return r; }

    friend std::ostream & operator<<(std::ostream & out, mpz const & v);

    std::string to_string() const;
};

struct mpz_cmp_fn {
    int operator()(mpz const & v1, mpz const & v2) const { return cmp(v1, v2); }
};
}
