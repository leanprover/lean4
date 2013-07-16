/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#pragma once
#include "mpz.h"

namespace lean {

// Wrapper for GMP rationals
class mpq {
    mpq_t m_val;
    static mpz_t const & zval(mpz const & v) { return v.m_val; }
    static mpz_t & zval(mpz & v) { return v.m_val; }
public:
    mpq & operator=(mpz const & v) { mpq_set_z(m_val, v.m_val); return *this; }
    mpq & operator=(mpq const & v) { mpq_set(m_val, v.m_val); return *this; }
    mpq & operator=(char const * v) { mpq_set_str(m_val, v, 10); return *this; }
    mpq & operator=(unsigned long int v) { mpq_set_ui(m_val, v, 1u); return *this; }
    mpq & operator=(long int v) { mpq_set_si(m_val, v, 1); return *this; }
    mpq & operator=(unsigned int v) { return operator=(static_cast<unsigned long int>(v)); }
    mpq & operator=(int v) { return operator=(static_cast<long int>(v)); }

    mpq() { mpq_init(m_val); }
    mpq(mpq const & v):mpq() { operator=(v); }
    mpq(mpz const & v):mpq() { operator=(v); }
    mpq(mpq && s):mpq() { mpq_swap(m_val, s.m_val); }
    mpq(char const * v):mpq() { operator=(v); }
    mpq(unsigned long int v):mpq() { operator=(v); }
    mpq(long int v):mpq() { operator=(v); }
    mpq(unsigned int v):mpq() { operator=(v); }
    mpq(int v):mpq() { operator=(v); }
    mpq(unsigned long int n, unsigned long int d):mpq() { mpq_set_ui(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(long int n, long int d):mpq() { mpq_set_si(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(unsigned int n, unsigned int d):mpq() { mpq_set_ui(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(int n, int d):mpq() { mpq_set_si(m_val, n, d); mpq_canonicalize(m_val); }
    mpq(double v):mpq() { mpq_set_d(m_val, v); }
    ~mpq() { mpq_clear(m_val); }

    void neg() { mpq_neg(m_val, m_val); }
    void abs() { mpq_abs(m_val, m_val); }
    void inv() { mpq_inv(m_val, m_val); }

    friend mpq abs(mpq a) { a.abs(); return a; }
    friend mpq neg(mpq a) { a.neg(); return a; }
    friend mpq inv(mpq a) { a.inv(); return a; }
    
    int sgn() const { return mpq_sgn(m_val); }
    friend int sgn(mpq const & a) { return a.sgn(); }
    DEFINE_SIGN_METHODS()

    unsigned hash() const { return static_cast<unsigned>(mpz_get_si(mpq_numref(m_val))); }

    void swap(mpq & v) { mpq_swap(m_val, v.m_val); }
    void swap_numerator(mpz & v) { mpz_swap(mpq_numref(m_val), v.m_val); mpq_canonicalize(m_val); }
    void swap_denominator(mpz & v) { mpz_swap(mpq_denref(m_val), v.m_val); mpq_canonicalize(m_val); }

    double get_double() const { return mpq_get_d(m_val); }

    bool is_integer() const { return mpz_cmp_ui(mpq_denref(m_val), 1u) == 0; }

    friend int cmp(mpq const & a, mpq const & b) { return mpq_cmp(a.m_val, b.m_val); }
    DEFINE_ORDER_OPS(mpq)
    friend bool operator==(mpq const & a, mpq const & b) { return mpq_equal(a.m_val, b.m_val) != 0; }
    friend bool operator==(mpq const & a, mpz const & b) { return a.is_integer() && mpz_cmp(mpq_numref(a.m_val), zval(b)) == 0; }
    friend bool operator==(mpq const & a, unsigned long int b) { return a.is_integer() && mpz_cmp_ui(mpq_numref(a.m_val), b) == 0; }
    friend bool operator==(mpq const & a, long int b) { return a.is_integer() && mpz_cmp_si(mpq_numref(a.m_val), b) == 0; }
    friend bool operator==(mpq const & a, unsigned int b) { return a.is_integer() && mpz_cmp_ui(mpq_numref(a.m_val), b) == 0; }
    friend bool operator==(mpq const & a, int b) { return a.is_integer() && mpz_cmp_si(mpq_numref(a.m_val), b) == 0; }
    friend bool operator==(mpz const & a, mpq const & b) { return operator==(b, a); }
    friend bool operator==(unsigned long int a, mpq const & b) { return operator==(b, a); }
    friend bool operator==(long int a, mpq const & b) { return operator==(b, a); }
    friend bool operator==(unsigned int a, mpq const & b) { return operator==(b, a); }
    friend bool operator==(int a, mpq const & b) { return operator==(b, a); }
    friend bool operator!=(mpq const & a, mpq const & b) { return !operator==(a,b); }
    friend bool operator!=(mpq const & a, mpz const & b) { return !operator==(a,b); }
    friend bool operator!=(mpz const & a, mpq const & b) { return !operator==(a,b); }
    friend bool operator!=(mpq const & a, unsigned long int b) { return !operator==(a,b); }
    friend bool operator!=(mpq const & a, long int b) { return !operator==(a,b); }
    friend bool operator!=(mpq const & a, unsigned int b) { return !operator==(a,b); }
    friend bool operator!=(mpq const & a, int b) { return !operator==(a,b); }
    friend bool operator!=(unsigned long int a, mpq const & b) { return !operator==(a,b); }
    friend bool operator!=(unsigned int a, mpq const & b) { return !operator==(a,b); }
    friend bool operator!=(long int a, mpq const & b) { return !operator==(a,b); }
    friend bool operator!=(int a, mpq const & b) { return !operator==(a,b); }
    
    mpq & operator+=(mpq const & o) { mpq_add(m_val, m_val, o.m_val); return *this; }
    mpq & operator+=(unsigned int k) { mpz_addmul_ui(mpq_numref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator+=(int k) { if (k >= 0) return operator+=(static_cast<unsigned int>(k)); else return operator-=(static_cast<unsigned int>(-k)); }
    mpq & operator-=(mpq const & o) { mpq_sub(m_val, m_val, o.m_val); return *this; }
    mpq & operator-=(unsigned int k) { mpz_submul_ui(mpq_numref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator-=(int k) { if (k >= 0) return operator-=(static_cast<unsigned int>(k)); else return operator+=(static_cast<unsigned int>(-k)); }
    mpq & operator*=(mpq const & o) { mpq_mul(m_val, m_val, o.m_val); return *this; }
    mpq & operator*=(unsigned int k) { mpz_mul_ui(mpq_numref(m_val), mpq_numref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator*=(int k) { mpz_mul_si(mpq_numref(m_val), mpq_numref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator/=(mpq const & o) { mpq_div(m_val, m_val, o.m_val); return *this; }
    mpq & operator/=(unsigned int k) { mpz_mul_ui(mpq_denref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    mpq & operator/=(int k) { mpz_mul_si(mpq_denref(m_val), mpq_denref(m_val), k); mpq_canonicalize(m_val); return *this; }
    DEFINE_ARITH_OPS(mpq)

    mpq & operator++() { return operator+=(1); }
    mpq & operator--() { return operator-=(1); }
    mpq operator++(int) { mpq r(*this); ++(*this); return r; }
    mpq operator--(int) { mpq r(*this); --(*this); return r; }
    
    mpz get_numerator() const { return mpz(mpq_numref(m_val)); }
    mpz get_denominator() const { return mpz(mpq_denref(m_val)); }

    friend std::ostream & operator<<(std::ostream & out, mpq const & v);

    void floor();
    void ceil();
    friend mpz floor(mpq const & a);
    friend mpz ceil(mpq const & a);
};

}
