/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/debug.h"
#include "util/int64.h"
#include "util/numerics/remainder.h"
#include "util/numerics/primes.h"
#include "util/numerics/power.h"
#include "util/numerics/numeric_traits.h"

namespace lean {
/**
   \brief The Z/pZ field (the set of integers modulo a prime p).
   We use machine integers to represent the values. That is, we only
   consider primes < 2^32 - 1.

   The values are encoded as a pair (value, p). We want to be able to
   dynamically change the prime p. This feature is needed when
   implementing some algorithms based on modular arithmetic.
*/
class zpz {
    unsigned m_value;
    unsigned m_p;
    bool is_normalized() const { return m_value < m_p; }
    void normalize() { m_value %= m_p; }
public:
    zpz():m_value(0), m_p(2) {}
    zpz(unsigned v, unsigned p):m_value(v), m_p(p) { lean_assert(is_prime(p)); }

    unsigned p() { return m_p; }
    unsigned hash() const { return m_value; }
    unsigned get_unsigned_int() const { return m_value; }
    void set_p(unsigned p) { lean_assert(is_prime(p)); m_p = p; normalize(); }

    friend void swap(zpz & a, zpz & b) { std::swap(a.m_value, b.m_value); std::swap(a.m_p, b.m_p); }

    friend bool operator==(zpz const & a, zpz const & b) { return a.m_value == b.m_value; }
    friend bool operator!=(zpz const & a, zpz const & b) { return !(a == b); }
    friend bool operator<(zpz const & a, zpz const & b)  { return a.m_value < b.m_value; }
    friend bool operator>(zpz const & a, zpz const & b)  { return a.m_value > b.m_value; }
    friend bool operator<=(zpz const & a, zpz const & b) { return a.m_value <= b.m_value; }
    friend bool operator>=(zpz const & a, zpz const & b) { return a.m_value >= b.m_value; }

    friend bool operator==(zpz const & a, unsigned b) { return a.m_value == b; }
    friend bool operator!=(zpz const & a, unsigned b) { return !(a == b); }
    friend bool operator<(zpz const & a, unsigned b)  { return a.m_value < b; }
    friend bool operator>(zpz const & a, unsigned b)  { return a.m_value > b; }
    friend bool operator<=(zpz const & a, unsigned b) { return a.m_value <= b; }
    friend bool operator>=(zpz const & a, unsigned b) { return a.m_value >= b; }

    friend bool operator==(unsigned a, zpz const & b) { return a == b.m_value; }
    friend bool operator!=(unsigned a, zpz const & b) { return !(a == b); }
    friend bool operator<(unsigned a, zpz const & b)  { return a < b.m_value; }
    friend bool operator>(unsigned a, zpz const & b)  { return a > b.m_value; }
    friend bool operator<=(unsigned a, zpz const & b) { return a <= b.m_value; }
    friend bool operator>=(unsigned a, zpz const & b) { return a >= b.m_value; }

    zpz & operator=(zpz const & v) { m_value = v.m_value; m_p = v.m_p; lean_assert(is_normalized()); return *this; }
    zpz & operator=(unsigned v)    { m_value = v; normalize(); return *this; }

    zpz & operator+=(unsigned v)    { m_value = (static_cast<uint64>(m_value) + static_cast<uint64>(v)) % m_p; return *this; }
    zpz & operator+=(zpz const & v) { return operator+=(v.m_value); }

    zpz & operator*=(unsigned v)    { m_value = (static_cast<uint64>(m_value) * static_cast<uint64>(v)) % m_p; return *this; }
    zpz & operator*=(zpz const & v) { return operator*=(v.m_value); }

    zpz & operator-=(unsigned v)    { m_value = remainder(static_cast<int64>(m_value) - static_cast<int64>(v), static_cast<int64>(m_p)); return *this; }
    zpz & operator-=(zpz const & v) { return operator-=(v.m_value); }

    zpz & operator++() { m_value++; if (m_value == m_p) m_value = 0; return *this; }
    zpz & operator--() { if (m_value == 0) m_value = m_p - 1; else m_value--; return *this; }
    zpz operator++(int) { zpz tmp(*this); operator++(); return tmp; }
    zpz operator--(int) { zpz tmp(*this); operator--(); return tmp; }

    void inv();
    void neg() { m_value = remainder(-static_cast<int64>(m_value), static_cast<int64>(m_p)); }

    zpz & operator/=(zpz v) { v.inv(); return operator*=(v); return *this; }
    zpz & operator/=(unsigned v) { return operator/=(zpz(v, m_p)); }

    friend zpz operator+(zpz a, zpz const & b) { return a += b; }
    friend zpz operator+(zpz a, unsigned b)    { return a += b; }
    friend zpz operator+(unsigned a, zpz b)    { return b += a; }

    friend zpz operator-(zpz a, zpz const & b) { return a -= b; }
    friend zpz operator-(zpz a, unsigned b)    { return a -= b; }
    friend zpz operator-(unsigned a, zpz b)    { b.neg(); return b += a; }

    friend zpz operator*(zpz a, zpz const & b) { return a *= b; }
    friend zpz operator*(zpz a, unsigned b)    { return a *= b; }
    friend zpz operator*(unsigned a, zpz b)    { return b *= a; }

    friend zpz operator/(zpz a, zpz const & b) { return a /= b; }
    friend zpz operator/(zpz a, unsigned b)    { return a /= b; }
    friend zpz operator/(unsigned a, zpz b)    { b.inv(); return b *= a; }

    friend std::ostream & operator<<(std::ostream & out, zpz const & z) { out << z.m_value; return out; }
};

template<>
class numeric_traits<zpz> {
public:
    static bool precise() { return true; }
    static bool is_zero(zpz const & v) { return v == 0; }
    static bool is_pos(zpz const & v)  { return v > 0; }
    static bool is_neg(zpz const & )  { return false; }
    static void set_rounding(bool ) {}
    static void neg(zpz & v)   { v.neg(); }
    static void reset(zpz & v) { v = 0; }
    // v <- v^k
    static void power(zpz & v, unsigned k) { v = lean::power(v, k); }
    static zpz const & zero();
};

void initialize_zpz();
void finalize_zpz();
}
