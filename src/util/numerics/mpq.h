/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/numerics/mpz.h"

namespace lean {
class mpbq;

/**
   \brief Wrapper for GMP rationals
*/
class mpq {
    friend class mpfp;
    mpq_t m_val;
    static mpz_t const & zval(mpz const & v) { return v.m_val; }
    static mpz_t & zval(mpz & v) { return v.m_val; }
public:
    friend void swap(mpq & a, mpq & b) { mpq_swap(a.m_val, b.m_val); }
    friend void swap_numerator(mpq & a, mpz & b) { mpz_swap(mpq_numref(a.m_val), zval(b)); mpq_canonicalize(a.m_val); }
    friend void swap_denominator(mpq & a, mpz & b) { mpz_swap(mpq_denref(a.m_val), zval(b)); mpq_canonicalize(a.m_val); }

    mpq & operator=(mpz const & v) { mpq_set_z(m_val, v.m_val); return *this; }
    mpq & operator=(mpq const & v) { mpq_set(m_val, v.m_val); return *this; }
    mpq & operator=(mpq && v) { swap(*this, v); return *this; }
    mpq & operator=(mpbq const & b);
    mpq & operator=(char const * v) { mpq_set_str(m_val, v, 10); return *this; }
    mpq & operator=(unsigned long int v) { mpq_set_ui(m_val, v, 1u); return *this; }
    mpq & operator=(long int v) { mpq_set_si(m_val, v, 1); return *this; }
    mpq & operator=(unsigned int v) { return operator=(static_cast<unsigned long int>(v)); }
    mpq & operator=(int v) { return operator=(static_cast<long int>(v)); }
    mpq & operator=(double v) { mpq_set_d(m_val, v); return *this; }

    mpq() { mpq_init(m_val); }
    mpq(mpq const & v):mpq() { operator=(v); }
    mpq(mpq && s):mpq() { mpq_swap(m_val, s.m_val); }
    template<typename T> explicit mpq(T const & v):mpq() { operator=(v); }
    mpq(unsigned long int n, unsigned long int d):mpq() { mpq_set_ui(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(long int n, long int d):mpq() { mpq_set_si(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(unsigned int n, unsigned int d):mpq() { mpq_set_ui(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(int n, int d):mpq() { mpq_set_si(m_val, n, d); mpq_canonicalize(m_val); }
    ~mpq() { mpq_clear(m_val); }

    unsigned hash() const { return static_cast<unsigned>(mpz_get_si(mpq_numref(m_val))); }

    int sgn() const { return mpq_sgn(m_val); }
    friend int sgn(mpq const & a) { return a.sgn(); }
    bool is_pos() const { return sgn() > 0; }
    bool is_neg() const { return sgn() < 0; }
    bool is_zero() const { return sgn() == 0; }
    bool is_nonpos() const { return !is_pos(); }
    bool is_nonneg() const { return !is_neg(); }

    void neg() { mpq_neg(m_val, m_val); }
    friend mpq neg(mpq a) { a.neg(); return a; }

    void abs() { mpq_abs(m_val, m_val); }
    friend mpq abs(mpq a) { a.abs(); return a; }

    void inv() { mpq_inv(m_val, m_val); }
    friend mpq inv(mpq a) { a.inv(); return a; }

    double get_double() const { return mpq_get_d(m_val); }

    bool is_integer() const { return mpz_cmp_ui(mpq_denref(m_val), 1u) == 0; }

    friend int cmp(mpq const & a, mpq const & b) { return mpq_cmp(a.m_val, b.m_val); }
    friend int cmp(mpq const & a, mpz const & b);
    friend int cmp(mpq const & a, unsigned b) { return mpq_cmp_ui(a.m_val, b, 1); }
    friend int cmp(mpq const & a, int b) { return mpq_cmp_si(a.m_val, b, 1); }
    friend int cmp(mpq const & a, double b) { return static_cast<int>(a.get_double() - b); }

    friend bool operator<(mpq const & a, mpq const & b) { return cmp(a, b) < 0; }
    friend bool operator<(mpq const & a, mpz const & b) { return cmp(a, b) < 0; }
    friend bool operator<(mpq const & a, unsigned b) { return cmp(a, b) < 0; }
    friend bool operator<(mpq const & a, int b) { return cmp(a, b) < 0; }
    friend bool operator<(mpq const & a, double b) { return cmp(a, b) < 0; }
    friend bool operator<(mpz const & a, mpq const & b) { return cmp(b, a) > 0; }
    friend bool operator<(unsigned a, mpq const & b) { return cmp(b, a) > 0; }
    friend bool operator<(int a, mpq const & b) { return cmp(b, a) > 0; }
    friend bool operator<(double a, mpq const & b) { return cmp(b, a) > 0; }

    friend bool operator>(mpq const & a, mpq const & b) { return cmp(a, b) > 0; }
    friend bool operator>(mpq const & a, mpz const & b) { return cmp(a, b) > 0; }
    friend bool operator>(mpq const & a, unsigned b) { return cmp(a, b) > 0; }
    friend bool operator>(mpq const & a, int b) { return cmp(a, b) > 0; }
    friend bool operator>(mpq const & a, double b) { return cmp(a, b) > 0; }
    friend bool operator>(mpz const & a, mpq const & b) { return cmp(b, a) < 0; }
    friend bool operator>(unsigned a, mpq const & b) { return cmp(b, a) < 0; }
    friend bool operator>(int a, mpq const & b) { return cmp(b, a) < 0; }
    friend bool operator>(double a, mpq const & b) { return cmp(b, a) < 0; }

    friend bool operator<=(mpq const & a, mpq const & b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpq const & a, mpz const & b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpq const & a, unsigned b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpq const & a, int b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpq const & a, double b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpz const & a, mpq const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(unsigned a, mpq const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(int a, mpq const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(double a, mpq const & b) { return cmp(b, a) >= 0; }

    friend bool operator>=(mpq const & a, mpq const & b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpq const & a, mpz const & b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpq const & a, unsigned b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpq const & a, int b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpq const & a, double b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpz const & a, mpq const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(unsigned a, mpq const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(int a, mpq const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(double a, mpq const & b) { return cmp(b, a) <= 0; }

    friend bool operator==(mpq const & a, mpq const & b) { return mpq_equal(a.m_val, b.m_val) != 0; }
    friend bool operator==(mpq const & a, mpz const & b) { return a.is_integer() && mpz_cmp(mpq_numref(a.m_val), zval(b)) == 0; }
    friend bool operator==(mpq const & a, unsigned int b) { return a.is_integer() && mpz_cmp_ui(mpq_numref(a.m_val), b) == 0; }
    friend bool operator==(mpq const & a, int b) { return a.is_integer() && mpz_cmp_si(mpq_numref(a.m_val), b) == 0; }
    friend bool operator==(mpz const & a, mpq const & b) { return operator==(b, a); }
    friend bool operator==(unsigned int a, mpq const & b) { return operator==(b, a); }
    friend bool operator==(int a, mpq const & b) { return operator==(b, a); }

    friend bool operator!=(mpq const & a, mpq const & b) { return !operator==(a, b); }
    friend bool operator!=(mpq const & a, mpz const & b) { return !operator==(a, b); }
    friend bool operator!=(mpq const & a, unsigned int b) { return !operator==(a, b); }
    friend bool operator!=(mpq const & a, int b) { return !operator==(a, b); }
    friend bool operator!=(mpz const & a, mpq const & b) { return !operator==(a, b); }
    friend bool operator!=(unsigned int a, mpq const & b) { return !operator==(a, b); }
    friend bool operator!=(int a, mpq const & b) { return !operator==(a, b); }

    mpq & operator+=(mpq const & o) { mpq_add(m_val, m_val, o.m_val); return *this; }
    mpq & operator+=(mpz const & o) { mpz_addmul(mpq_numref(m_val), mpq_denref(m_val), o.m_val); mpq_canonicalize(m_val); return *this; }
    mpq & operator+=(unsigned int k) { mpz_addmul_ui(mpq_numref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator+=(int k) { if (k >= 0) return operator+=(static_cast<unsigned int>(k)); else return operator-=(static_cast<unsigned int>(-k)); }

    mpq & operator-=(mpq const & o) { mpq_sub(m_val, m_val, o.m_val); return *this; }
    mpq & operator-=(mpz const & o) { mpz_submul(mpq_numref(m_val), mpq_denref(m_val), o.m_val); mpq_canonicalize(m_val); return *this; }
    mpq & operator-=(unsigned int k) { mpz_submul_ui(mpq_numref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator-=(int k) { if (k >= 0) return operator-=(static_cast<unsigned int>(k)); else return operator+=(static_cast<unsigned int>(-k)); }

    mpq & operator*=(mpq const & o) { mpq_mul(m_val, m_val, o.m_val); return *this; }
    mpq & operator*=(mpz const & o) { mpz_mul(mpq_numref(m_val), mpq_numref(m_val), o.m_val); mpq_canonicalize(m_val); return *this; }
    mpq & operator*=(unsigned int k) { mpz_mul_ui(mpq_numref(m_val), mpq_numref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator*=(int k) { mpz_mul_si(mpq_numref(m_val), mpq_numref(m_val), k); mpq_canonicalize(m_val); return *this; }

    mpq & operator/=(mpq const & o) { mpq_div(m_val, m_val, o.m_val); return *this; }
    mpq & operator/=(mpz const & o) { mpz_mul(mpq_denref(m_val), mpq_denref(m_val), o.m_val); mpq_canonicalize(m_val); return *this; }
    mpq & operator/=(unsigned int k) { mpz_mul_ui(mpq_denref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator/=(int k) { mpz_mul_si(mpq_denref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }

    friend mpq operator+(mpq a, mpq const & b) { return a += b; }
    friend mpq operator+(mpq a, mpz const & b) { return a += b; }
    friend mpq operator+(mpq a, unsigned b)  { return a += b; }
    friend mpq operator+(mpq a, int b)  { return a += b; }
    friend mpq operator+(mpz const & a, mpq b) { return b += a; }
    friend mpq operator+(unsigned a, mpq b) { return b += a; }
    friend mpq operator+(int a, mpq b) { return b += a; }

    friend mpq operator-(mpq a, mpq const & b) { return a -= b; }
    friend mpq operator-(mpq a, mpz const & b) { return a -= b; }
    friend mpq operator-(mpq a, unsigned b) { return a -= b; }
    friend mpq operator-(mpq a, int b) { return a -= b; }
    friend mpq operator-(mpz const & a, mpq b) { b.neg(); return b += a; }
    friend mpq operator-(unsigned a, mpq b) { b.neg(); return b += a; }
    friend mpq operator-(int a, mpq b) { b.neg(); return b += a; }

    friend mpq operator*(mpq a, mpq const & b) { return a *= b; }
    friend mpq operator*(mpq a, mpz const & b) { return a *= b; }
    friend mpq operator*(mpq a, unsigned b) { return a *= b; }
    friend mpq operator*(mpq a, int b) { return a *= b; }
    friend mpq operator*(mpz const & a, mpq b) { return b *= a; }
    friend mpq operator*(unsigned a, mpq b) { return b *= a; }
    friend mpq operator*(int a, mpq b) { return b *= a; }

    friend mpq operator/(mpq a, mpq const & b) { return a /= b; }
    friend mpq operator/(mpq a, mpz const & b) { return a /= b; }
    friend mpq operator/(mpq a, unsigned b) { return a /= b; }
    friend mpq operator/(mpq a, int b) { return a /= b; }
    friend mpq operator/(mpz const & a, mpq b) { b.inv(); return b *= a; }
    friend mpq operator/(unsigned a, mpq b) { b.inv(); return b *= a; }
    friend mpq operator/(int a, mpq b) { b.inv(); return b *= a; }

    mpq & operator++() { return operator+=(1); }
    mpq operator++(int) { mpq r(*this); ++(*this); return r; }

    mpq & operator--() { return operator-=(1); }
    mpq operator--(int) { mpq r(*this); --(*this); return r; }

    mpq operator-() const { mpq t = *this; t.neg(); return t; }

    // a <- numerator(b)
    friend void numerator(mpz & a, mpq const & b) { mpz_set(zval(a), mpq_numref(b.m_val)); }
    // a <- denominator(b)
    friend void denominator(mpz & a, mpq const & b) { mpz_set(zval(a), mpq_denref(b.m_val)); }

    mpz get_numerator() const { mpz r; numerator(r, *this); return r; }
    mpz get_denominator() const { mpz r; denominator(r, *this); return r; }

    void floor();
    friend mpz floor(mpq const & a);

    void ceil();
    friend mpz ceil(mpq const & a);

    friend void power(mpq & a, mpq const & b, unsigned k);
    friend void _power(mpq & a, mpq const & b, unsigned k) { power(a, b, k); }
    friend mpq pow(mpq a, unsigned k) { power(a, a, k); return a; }

    friend std::ostream & operator<<(std::ostream & out, mpq const & v);

    friend void display_decimal(std::ostream & out, mpq const & a, unsigned prec);

    class decimal {
        mpq const & m_val;
        unsigned     m_prec;
    public:
        decimal(mpq const & val, unsigned prec = 10):m_val(val), m_prec(prec) {}
        friend std::ostream & operator<<(std::ostream & out, decimal const & d) { display_decimal(out, d.m_val, d.m_prec); return out; }
    };
};

template<>
class numeric_traits<mpq> {
    static mpq * pi_l;
    static mpq * pi_n;
    static mpq * pi_u;
public:
    static void initialize();
    static void finalize();

    static bool precise() { return true; }
    static bool is_zero(mpq const &  v) { return v.is_zero(); }
    static bool is_pos(mpq const & v) { return v.is_pos(); }
    static bool is_neg(mpq const & v) { return v.is_neg(); }
    static void set_rounding(bool ) {}
    static void neg(mpq & v) { v.neg(); }
    static void inv(mpq & v) { v.inv(); }
    static void reset(mpq & v) { v = 0; }
    static mpq const & zero();
    static mpq const & one();

    static void power(mpq & v, unsigned k) { _power(v, v, k); }
    static void abs(mpq & v) { v.abs(); }
    static void ceil(mpq & v) { v.ceil(); }
    static void floor(mpq & v) { v.floor(); }
    static double get_double(mpq const & d) { return d.get_double(); }

    // constants
    static inline mpq pi_lower()       { return *pi_l;     }
    static inline mpq pi()             { return *pi_n;     }
    static inline mpq pi_upper()       { return *pi_u;     }
    static inline mpq pi_half_lower()  { return *pi_l / 2; }
    static inline mpq pi_half()        { return *pi_n / 2; }
    static inline mpq pi_half_upper()  { return *pi_u / 2; }
    static inline mpq pi_twice_lower() { return *pi_l * 2; }
    static inline mpq pi_twice()       { return *pi_n * 2; }
    static inline mpq pi_twice_upper() { return *pi_u * 2; }

    // Transcendental functions
    static void exp(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void exp2(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void exp10(mpq & ) { lean_unreachable(); } // LCOV_EXCL_LINE
    static void log(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void log2(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void log10(mpq & ) { lean_unreachable(); } // LCOV_EXCL_LINE
    static void sin(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void cos(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void tan(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void sec(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void csc(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void cot(mpq & )   { lean_unreachable(); } // LCOV_EXCL_LINE
    static void asin(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void acos(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void atan(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void sinh(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void cosh(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void tanh(mpq & )  { lean_unreachable(); } // LCOV_EXCL_LINE
    static void asinh(mpq & ) { lean_unreachable(); } // LCOV_EXCL_LINE
    static void acosh(mpq & ) { lean_unreachable(); } // LCOV_EXCL_LINE
    static void atanh(mpq & ) { lean_unreachable(); } // LCOV_EXCL_LINE
};

serializer & operator<<(serializer & s, mpq const & n);
mpq read_mpq(deserializer & d);
inline deserializer & operator>>(deserializer & d, mpq & n) { n = read_mpq(d); return d; }

void initialize_mpq();
void finalize_mpq();
}
