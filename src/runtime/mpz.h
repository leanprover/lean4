/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstddef>
#ifdef LEAN_USE_GMP
#include <gmp.h>
#else
#include "runtime/mpn.h"
#endif
#include <string>
#include <iostream>
#include <limits>
#include <lean/lean.h>
#include "runtime/int.h"
#include "runtime/debug.h"

namespace lean {

/** \brief Wrapper for GMP integers */
class LEAN_EXPORT mpz {
    friend class object_compactor;
    friend class compacted_region;
#ifdef LEAN_USE_GMP
    mpz_t m_val;
    mpz(__mpz_struct const * v) { mpz_init_set(m_val, v); }
#else
    bool        m_sign;
    size_t      m_size;
    mpn_digit * m_digits;
    void allocate(size_t s);
    void init();
    void init_str(char const * v);
    void init_uint(unsigned int v);
    void init_int(int v);
    void init_uint64(uint64 v);
    void init_int64(int64 v);
    void init_mpz(mpz const & v);
    void set(size_t sz, mpn_digit const * digits);
    mpz & add(bool sign, size_t sz, mpn_digit const * digits);
    mpz & mul(bool sign, size_t sz, mpn_digit const * digits);
    mpz & div(bool sign, size_t sz, mpn_digit const * digits);
    mpz & rem(size_t sz, mpn_digit const * digits);
#endif
public:
    mpz();
#ifdef LEAN_USE_GMP
    explicit mpz(mpz_t v);
#endif
    explicit mpz(char const * v);
    explicit mpz(unsigned int v);
    explicit mpz(int v);
    explicit mpz(uint64 v);
    explicit mpz(int64 v);
    static mpz of_size_t(size_t v) {
        if (sizeof(size_t) == sizeof(uint64)) // NOLINT
            return mpz((uint64) v); // NOLINT
        else
            return mpz((unsigned) v); // NOLINT
    }
    mpz(mpz const & s);
    mpz(mpz && s);
    ~mpz();

#ifdef LEAN_USE_GMP
    void set(mpz_t r) const;
#endif

    friend void swap(mpz & a, mpz & b);

    unsigned hash() const {
#ifdef LEAN_USE_GMP
        return static_cast<unsigned>(mpz_get_si(m_val));
#else
        return m_digits[0];
#endif
    }

    int sgn() const;

    friend int sgn(mpz const & a) { return a.sgn(); }

    bool is_pos() const {
#ifdef LEAN_USE_GMP
        return sgn() > 0;
#else
        return !m_sign && (m_size > 1 || m_digits[0] != 0);
#endif
    }

    bool is_neg() const {
#ifdef LEAN_USE_GMP
        return sgn() < 0;
#else
        return m_sign;
#endif
    }

    bool is_zero() const {
#ifdef LEAN_USE_GMP
        return sgn() == 0;
#else
        return m_size == 1 && m_digits[0] == 0;
#endif
    }

    bool is_nonpos() const { return !is_pos(); }

    bool is_nonneg() const { return !is_neg(); }

    void neg() {
#ifdef LEAN_USE_GMP
        mpz_neg(m_val, m_val);
#else
        if (!is_zero())
            m_sign = !m_sign;
#endif
    }

    friend mpz neg(mpz a) { a.neg(); return a; }

    void abs() {
#ifdef LEAN_USE_GMP
        mpz_abs(m_val, m_val);
#else
        m_sign = false;
#endif
    }

    friend mpz abs(mpz a) { a.abs(); return a; }

    bool is_int() const;
    bool is_unsigned_int() const;
    bool is_size_t() const;

    int get_int() const;
    unsigned int get_unsigned_int() const;
    size_t get_size_t() const;

    mpz & operator=(mpz const & v);
    mpz & operator=(mpz && v) { swap(*this, v); return *this; }
    mpz & operator=(char const * v);
    mpz & operator=(unsigned int v);
    mpz & operator=(int v);

    LEAN_EXPORT friend int cmp(mpz const & a, mpz const & b);
    LEAN_EXPORT friend int cmp(mpz const & a, unsigned b);
    LEAN_EXPORT friend int cmp(mpz const & a, int b);

    friend bool operator<(mpz const & a, mpz const & b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, unsigned b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, int b) { return cmp(a, b) < 0; }
    friend bool operator<(unsigned a, mpz const & b) { return cmp(b, a) > 0; }
    friend bool operator<(int a, mpz const & b) { return cmp(b, a) > 0; }

    friend bool operator>(mpz const & a, mpz const & b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, unsigned b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, int b) { return cmp(a, b) > 0; }
    friend bool operator>(unsigned a, mpz const & b) { return cmp(b, a) < 0; }
    friend bool operator>(int a, mpz const & b) { return cmp(b, a) < 0; }

    friend bool operator<=(mpz const & a, mpz const & b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, unsigned b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, int b) { return cmp(a, b) <= 0; }
    friend bool operator<=(unsigned a, mpz const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(int a, mpz const & b) { return cmp(b, a) >= 0; }

    friend bool operator>=(mpz const & a, mpz const & b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, unsigned b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, int b) { return cmp(a, b) >= 0; }
    friend bool operator>=(unsigned a, mpz const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(int a, mpz const & b) { return cmp(b, a) <= 0; }

    friend bool operator==(mpz const & a, mpz const & b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, unsigned b) { return cmp(a, b) == 0; }
    friend bool operator==(mpz const & a, int b) { return cmp(a, b) == 0; }
    friend bool operator==(unsigned a, mpz const & b) { return cmp(b, a) == 0; }
    friend bool operator==(int a, mpz const & b) { return cmp(b, a) == 0; }

    friend bool operator!=(mpz const & a, mpz const & b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, unsigned b) { return cmp(a, b) != 0; }
    friend bool operator!=(mpz const & a, int b) { return cmp(a, b) != 0; }
    friend bool operator!=(unsigned a, mpz const & b) { return cmp(b, a) != 0; }
    friend bool operator!=(int a, mpz const & b) { return cmp(b, a) != 0; }

    mpz & operator+=(mpz const & o);
    mpz & operator+=(unsigned u);
    mpz & operator+=(int u);
    mpz & operator+=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this += mpz(u) : *this += static_cast<unsigned>(u); }

    mpz & operator-=(mpz const & o);
    mpz & operator-=(unsigned u);
    mpz & operator-=(int u);
    mpz & operator-=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this -= mpz(u) : *this -= static_cast<unsigned>(u); }

    mpz & operator*=(mpz const & o);
    mpz & operator*=(unsigned u);
    mpz & operator*=(int u);
    mpz & operator*=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this *= mpz(u) : *this *= static_cast<unsigned>(u); }

    mpz & operator/=(mpz const & o);
    mpz & operator/=(unsigned u);
    mpz & operator/=(uint64 u) { return u > std::numeric_limits<unsigned>::max() ? *this /= mpz(u) : *this /= static_cast<unsigned>(u); }
    mpz & operator/=(int u) { return operator/=(mpz(u)); } // TODO(Leo): improve

    mpz & operator%=(mpz const & o);
    friend mpz rem(mpz const & a, mpz const & b) { mpz r(a); return r %= b; }

    mpz pow(unsigned int exp) const;

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

    friend mpz operator%(mpz a, mpz const & b) { return a %= b; }

    static mpz ediv(mpz const & n, mpz const & d);
    static mpz ediv(int n, mpz const & d) { return ediv(mpz(n), d); }
    static mpz ediv(mpz const& n, int d) { return ediv(n, mpz(d)); }

    static mpz emod(mpz const & n, mpz const & d);
    static mpz emod(int n, mpz const & d) { return emod(mpz(n), d); }
    static mpz emod(mpz const & n, int d) { return emod(n, mpz(d)); };

    mpz & operator&=(mpz const & o);
    mpz & operator|=(mpz const & o);
    mpz & operator^=(mpz const & o);

    friend mpz operator&(mpz a, mpz const & b) { return a &= b; }
    friend mpz operator|(mpz a, mpz const & b) { return a |= b; }
    friend mpz operator^(mpz a, mpz const & b) { return a ^= b; }

    // a <- b * 2^k
    friend void mul2k(mpz & a, mpz const & b, unsigned k);
    // a <- b / 2^k
    friend void div2k(mpz & a, mpz const & b, unsigned k);

    uint8 mod8() const;
    uint16 mod16() const;
    uint32 mod32() const;
    uint64 mod64() const;

    int8 smod8() const;
    int16 smod16() const;
    int32 smod32() const;
    int64 smod64() const;

    /**
       \brief Return the position of the most significant bit.
       Return 0 if the number is negative
    */
    size_t log2() const;

    friend void power(mpz & a, mpz const & b, unsigned k);
    friend void _power(mpz & a, mpz const & b, unsigned k) { power(a, b, k); }
    friend mpz pow(mpz a, unsigned k) { power(a, a, k); return a; }

    friend void gcd(mpz & g, mpz const & a, mpz const & b);
    friend mpz gcd(mpz const & a, mpz const & b) { mpz r; gcd(r, a, b); return r; }

    LEAN_EXPORT friend std::ostream & operator<<(std::ostream & out, mpz const & v);

    std::string to_string() const;
};

struct mpz_cmp_fn {
    int operator()(mpz const & v1, mpz const & v2) const { return cmp(v1, v2); }
};
}
