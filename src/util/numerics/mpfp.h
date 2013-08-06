/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <stdint.h>
#include <mpfr.h>
#include "mpz.h"
#include "mpq.h"
#include "mpbq.h"

namespace lean {
/**
   \brief Wrapper for MPFR
*/
class mpfp {
    mpfr_t m_val;

//    static mpfr_t const & zval(mpz const & v) { return v.m_val; }
//    static mpfr_t & zval(mpz & v) { return v.m_val; }
public:
    // friend void swap(mpfp & a, mpfp & b) { mpfr_swap(a.m_val, b.m_val); }
    // friend void swap_numerator(mpfp & a, mpz & b) { mpz_swap(mpfr_numref(a.m_val), zval(b)); mpfr_canonicalize(a.m_val); }
    // friend void swap_denominator(mpfp & a, mpz & b) { mpz_swap(mpfr_denref(a.m_val), zval(b)); mpfr_canonicalize(a.m_val); }

    // Setter functions
    mpfp & set(mpfp const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set(m_val, v.m_val, MPFR_RNDN); return *this;
    }
    mpfp & set(unsigned long int const v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_ui(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(long int const v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_si(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(float const v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_flt(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(double const v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_d(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(long double const v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_ld(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(mpz_t const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_z(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(mpq_t const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_q(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(mpf_t const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_f(m_val, v, MPFR_RNDN); return *this;
    }
    mpfp & set(mpz   const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_z(m_val, v.m_val, MPFR_RNDN); return *this;
    }
    mpfp & set(mpq   const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_q(m_val, v.m_val, MPFR_RNDN); return *this;
    }
    mpfp & set(mpbq  const & v, mpfr_rnd_t rnd = MPFR_RNDN) {
        mpfr_set_z(m_val, v.m_num.m_val, rnd);   // this = m_num
        mpfr_div_2ui(m_val, m_val, v.m_k, rnd);  // this = m_num / (2^k)
        return *this;
    }

    // Assignment operators
    mpfp & operator=(mpfp const & v)            { return set(v); }
    mpfp & operator=(unsigned long int const v) { return set(v); }
    mpfp & operator=(long int const v)          { return set(v); }
    mpfp & operator=(float const v)             { return set(v); }
    mpfp & operator=(double const v)            { return set(v); }
    mpfp & operator=(long double const v)       { return set(v); }
    mpfp & operator=(mpz_t const & v)           { return set(v); }
    mpfp & operator=(mpq_t const & v)           { return set(v); }
    mpfp & operator=(mpf_t const & v)           { return set(v); }
    mpfp & operator=(mpz   const & v)           { return set(v); }
    mpfp & operator=(mpq   const & v)           { return set(v); }
    mpfp & operator=(mpbq  const & v)           { return set(v); }

    // Basic Constructors
    mpfp() { mpfr_init(m_val); } // with default precision
    mpfp(mpfr_prec_t prec) { mpfr_init2(m_val, prec); }

    // Constructors using the default precision
    mpfp(float const v      ):mpfp() { set(v); }
    mpfp(double const v     ):mpfp() { set(v); }
    mpfp(long double const v):mpfp() { set(v); }
    mpfp(mpz_t const & v    ):mpfp() { set(v); }
    mpfp(mpq_t const & v    ):mpfp() { set(v); }
    mpfp(mpf_t const & v    ):mpfp() { set(v); }
    mpfp(mpz const & v      ):mpfp() { set(v); }
    mpfp(mpq const & v      ):mpfp() { set(v); }
    mpfp(mpbq const & v     ):mpfp() { set(v); }
    mpfp(mpfp const & v     ):mpfp(mpfr_get_prec(v.m_val)) { set(v); }

    // Constructors using the provided precision
    mpfp(float const v      , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(double const v     , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(long double const v, mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpz_t const & v    , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpq_t const & v    , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpf_t const & v    , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpz const & v      , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpq const & v      , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpbq const & v     , mpfr_prec_t p):mpfp(p) { set(v); }
    mpfp(mpfp const & v     , mpfr_prec_t p):mpfp(p) { set(v); }

    // Constructors using the provided precision and rounding mode
    mpfp(float const v      , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(double const v     , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(long double const v, mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpz_t const & v    , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpq_t const & v    , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpf_t const & v    , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpz const & v      , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpq const & v      , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpbq const & v     , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }
    mpfp(mpfp const & v     , mpfr_prec_t p, mpfr_rnd_t rnd):mpfp(p) { set(v, rnd); }

    // mpfr(mpfp && s):mpfr() { mpfr_swap(m_val, s.m_val); }
    // template<typename T> explicit mpfr(T const & v):mpfr() { operator=(v); }
    // mpfr(unsigned long int n, unsigned long int d):mpfr() { mpfr_set_ui(m_val, n, d); mpfr_canonicalize(m_val);}
    ~mpfp() { mpfr_clear(m_val); }

    unsigned hash() const { return static_cast<unsigned>(mpfr_get_si(m_val, MPFR_RNDN)); }

    int sgn() const { return mpfr_sgn(m_val); }
    friend int sgn(mpfp const & a) { return a.sgn(); }
    bool is_pos() const { return sgn() > 0; }
    bool is_neg() const { return sgn() < 0; }
    bool is_zero() const { return sgn() == 0; }
    bool is_nonpos() const { return !is_pos(); }
    bool is_nonneg() const { return !is_neg(); }

    void neg() { mpfr_neg(m_val, m_val, MPFR_RNDN); }
    friend mpfp neg(mpfp a) { a.neg(); return a; }

    // Math functions and theirs friend functions
    void abs(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_abs(m_val, m_val, rnd); }
    void exp(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_exp(m_val, m_val, rnd); }
    void exp2(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_exp2(m_val, m_val, rnd); }
    void exp10(mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_exp10(m_val, m_val, rnd); }
    void log(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_log(m_val, m_val, rnd); }
    void log2(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_log2(m_val, m_val, rnd); }
    void log10(mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_log10(m_val, m_val, rnd); }
    void sin(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_sin(m_val, m_val, rnd); }
    void cos(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_cos(m_val, m_val, rnd); }
    void tan(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_tan(m_val, m_val, rnd); }
    void sec(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_sec(m_val, m_val, rnd); }
    void csc(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_csc(m_val, m_val, rnd); }
    void cot(mpfr_rnd_t rnd = MPFR_RNDN)   { mpfr_cot(m_val, m_val, rnd); }
    void asin(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_asin(m_val, m_val, rnd); }
    void acos(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_acos(m_val, m_val, rnd); }
    void atan(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_atan(m_val, m_val, rnd); }
    void sinh(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_sinh(m_val, m_val, rnd); }
    void cosh(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_cosh(m_val, m_val, rnd); }
    void tanh(mpfr_rnd_t rnd = MPFR_RNDN)  { mpfr_tanh(m_val, m_val, rnd); }
    void asinh(mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_asinh(m_val, m_val, rnd); }
    void acosh(mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_acosh(m_val, m_val, rnd); }
    void atanh(mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_atanh(m_val, m_val, rnd); }
    friend mpfp abs(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.abs(rnd); return a; }
    friend mpfp exp(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.exp(rnd); return a; }
    friend mpfp exp2(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.exp2(rnd); return a; }
    friend mpfp exp10(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN) { a.exp10(rnd); return a; }
    friend mpfp log(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.log(rnd); return a; }
    friend mpfp log2(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.log2(rnd); return a; }
    friend mpfp log10(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN) { a.log10(rnd); return a; }
    friend mpfp sin(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.sin(rnd); return a; }
    friend mpfp cos(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.cos(rnd); return a; }
    friend mpfp tan(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.tan(rnd); return a; }
    friend mpfp sec(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.sec(rnd); return a; }
    friend mpfp csc(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.csc(rnd); return a; }
    friend mpfp cot(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)   { a.cot(rnd); return a; }
    friend mpfp asin(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.asin(rnd); return a; }
    friend mpfp acos(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.acos(rnd); return a; }
    friend mpfp atan(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.atan(rnd); return a; }
    friend mpfp sinh(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.sinh(rnd); return a; }
    friend mpfp cosh(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.cosh(rnd); return a; }
    friend mpfp tanh(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN)  { a.tanh(rnd); return a; }
    friend mpfp asinh(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN) { a.asinh(rnd); return a; }
    friend mpfp acosh(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN) { a.acosh(rnd); return a; }
    friend mpfp atanh(mpfp a, mpfr_rnd_t rnd = MPFR_RNDN) { a.atanh(rnd); return a; }

    // void inv() { mpfr_inv(m_val, m_val, MPFR_RNDN); }
    // friend mpfp inv(mpfp a) { a.inv(); return a; }
    double get_double(mpfr_rnd_t rnd = MPFR_RNDN) const { return mpfr_get_d(m_val, rnd); }
    float  get_float (mpfr_rnd_t rnd = MPFR_RNDN) const { return mpfr_get_flt(m_val, rnd); }

    // bool is_integer() const { return mpz_cmp_ui(mpfr_denref(m_val), 1u) == 0; }

    friend int cmp(mpfp const & a, mpfp const & b           ) { return mpfr_cmp(a.m_val, b.m_val); }
//    friend int cmp(mpfp const & a, mpz const & b);
    friend int cmp(mpfp const & a, unsigned long int const b) { return mpfr_cmp_ui(a.m_val, b); }
    friend int cmp(mpfp const & a, long int const b         ) { return mpfr_cmp_si(a.m_val, b); }
    friend int cmp(mpfp const & a, double const b           ) { return mpfr_cmp_d (a.m_val, b); }
    friend int cmp(mpfp const & a, long double const b      ) { return mpfr_cmp_ld(a.m_val, b); }
    friend int cmp(mpfp const & a, mpz_t const & b          ) { return mpfr_cmp_z (a.m_val, b); }
    friend int cmp(mpfp const & a, mpq_t const & b          ) { return mpfr_cmp_q (a.m_val, b); }
    friend int cmp(mpfp const & a, mpf_t const & b          ) { return mpfr_cmp_f (a.m_val, b); }
    /* TODO */
    // friend int cmp(mpfp const & a, mpz const & b) { return mpfr_cmp_(a.m_val, b); }
    // friend int cmp(mpfp const & a, mpq const & b) { return mpfr_cmp_(a.m_val, b); }
    // friend int cmp(mpfp const & a, mpbq const & b) { return mpfr_cmp_(a.m_val, b); }

    friend bool operator<(mpfp const & a, mpfp const & b           ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, mpz const & b            ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, unsigned long int const b) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, long int const b         ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, double const b           ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, long double const b      ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, mpz_t const & b          ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, mpq_t const & b          ) { return cmp(a, b) < 0; }
    friend bool operator<(mpfp const & a, mpf_t const & b          ) { return cmp(a, b) < 0; }

    friend bool operator<(mpz const & a            , mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(unsigned long int const a, mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(long int const a         , mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(double const a           , mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(long double const a      , mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(mpz_t const & a          , mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(mpq_t const & a          , mpfp const & b) { return cmp(b, a) > 0; }
    friend bool operator<(mpf_t const & a          , mpfp const & b) { return cmp(b, a) > 0; }

    friend bool operator>(mpfp const & a, mpfp const & b           ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, mpz const & b            ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, unsigned long int const b) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, long int const b         ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, double const b           ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, long double const b      ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, mpz_t const & b          ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, mpq_t const & b          ) { return cmp(a, b) > 0; }
    friend bool operator>(mpfp const & a, mpf_t const & b          ) { return cmp(a, b) > 0; }

    friend bool operator>(mpz const & a            , mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(unsigned long int const a, mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(long int const a         , mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(double const a           , mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(long double const a      , mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(mpz_t const & a          , mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(mpq_t const & a          , mpfp const & b) { return cmp(b, a) < 0; }
    friend bool operator>(mpf_t const & a          , mpfp const & b) { return cmp(b, a) < 0; }

    friend bool operator<=(mpfp const & a, mpfp const & b           ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, mpz const & b            ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, unsigned long int const b) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, long int const b         ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, double const b           ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, long double const b      ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, mpz_t const & b          ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, mpq_t const & b          ) { return cmp(a, b) <= 0; }
    friend bool operator<=(mpfp const & a, mpf_t const & b          ) { return cmp(a, b) <= 0; }

    friend bool operator<=(mpz const & a            , mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(unsigned long int const a, mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(long int const a         , mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(double const a           , mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(long double const a      , mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(mpz_t const & a          , mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(mpq_t const & a          , mpfp const & b) { return cmp(b, a) >= 0; }
    friend bool operator<=(mpf_t const & a          , mpfp const & b) { return cmp(b, a) >= 0; }

    friend bool operator>=(mpfp const & a, mpfp const & b           ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, mpz const & b            ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, unsigned long int const b) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, long int const b         ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, double const b           ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, long double const b      ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, mpz_t const & b          ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, mpq_t const & b          ) { return cmp(a, b) >= 0; }
    friend bool operator>=(mpfp const & a, mpf_t const & b          ) { return cmp(a, b) >= 0; }

    friend bool operator>=(mpz const & a            , mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(unsigned long int const a, mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(long int const a         , mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(double const a           , mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(long double const a      , mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(mpz_t const & a          , mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(mpq_t const & a          , mpfp const & b) { return cmp(b, a) <= 0; }
    friend bool operator>=(mpf_t const & a          , mpfp const & b) { return cmp(b, a) <= 0; }

    friend bool operator==(mpfp const & a, mpfp const & b) { return mpfr_equal_p(a.m_val, b.m_val) != 0; }
//    friend bool operator==(mpfp const & a, mpz const & b) { return a.is_integer() && mpz_cmp(mpfr_numref(a.m_val), zval(b)) == 0; }
    // friend bool operator==(mpfp const & a, unsigned int b) { return a.is_integer() && mpz_cmp_ui(mpfr_numref(a.m_val), b) == 0; }
    // friend bool operator==(mpfp const & a, int b) { return a.is_integer() && mpz_cmp_si(mpfr_numref(a.m_val), b) == 0; }
    // friend bool operator==(mpz const & a, mpfp const & b) { return operator==(b, a); }
    // friend bool operator==(unsigned int a, mpfp const & b) { return operator==(b, a); }
    // friend bool operator==(int a, mpfp const & b) { return operator==(b, a); }

    friend bool operator!=(mpfp const & a, mpfp const & b) { return !operator==(a,b); }
    // friend bool operator!=(mpfp const & a, mpz const & b) { return !operator==(a,b); }
    // friend bool operator!=(mpfp const & a, unsigned int b) { return !operator==(a,b); }
    // friend bool operator!=(mpfp const & a, int b) { return !operator==(a,b); }
    // friend bool operator!=(mpz const & a, mpfp const & b) { return !operator==(a,b); }
    // friend bool operator!=(unsigned int a, mpfp const & b) { return !operator==(a,b); }
    // friend bool operator!=(int a, mpfp const & b) { return !operator==(a,b); }

    mpfp & add(mpfp const & o, mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_add(m_val, m_val, o.m_val, rnd); return *this; }
    mpfp & operator+=(mpfp const & o) { return add(o); }
    // mpfp & operator+=(mpz const & o) { mpz_addmul(mpfr_numref(m_val), mpfr_denref(m_val), o.m_val); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator+=(unsigned int k) { mpz_addmul_ui(mpfr_numref(m_val), mpfr_denref(m_val), k); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator+=(int k) { if (k >= 0) return operator+=(static_cast<unsigned int>(k)); else return operator-=(static_cast<unsigned int>(-k)); }

    mpfp & sub(mpfp const & o, mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_sub(m_val, m_val, o.m_val, rnd); return *this; }
    mpfp & operator-=(mpfp const & o) { return sub(o); }
    // mpfp & operator-=(mpz const & o) { mpz_submul(mpfr_numref(m_val), mpfr_denref(m_val), o.m_val); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator-=(unsigned int k) { mpz_submul_ui(mpfr_numref(m_val), mpfr_denref(m_val), k); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator-=(int k) { if (k >= 0) return operator-=(static_cast<unsigned int>(k)); else return operator+=(static_cast<unsigned int>(-k)); }

    mpfp & mul(mpfp const & o, mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_mul(m_val, m_val, o.m_val, rnd); return *this; }
    mpfp & operator*=(mpfp const & o) { return mul(o); }
    // mpfp & operator*=(mpz const & o) { mpz_mul(mpfr_numref(m_val), mpfr_numref(m_val), o.m_val); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator*=(unsigned int k) { mpz_mul_ui(mpfr_numref(m_val), mpfr_numref(m_val), k); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator*=(int k) { mpz_mul_si(mpfr_numref(m_val), mpfr_numref(m_val), k); mpfr_canonicalize(m_val); return *this; }

    mpfp & div(mpfp const & o, mpfr_rnd_t rnd = MPFR_RNDN) { mpfr_div(m_val, m_val, o.m_val, rnd); return *this; }
    mpfp & operator/=(mpfp const & o) { return div(o); }
    // mpfp & operator/=(mpz const & o) { mpz_mul(mpfr_denref(m_val), mpfr_denref(m_val), o.m_val); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator/=(unsigned int k) { mpz_mul_ui(mpfr_denref(m_val), mpfr_denref(m_val), k); mpfr_canonicalize(m_val); return *this; }
    // mpfp & operator/=(int k) { mpz_mul_si(mpfr_denref(m_val), mpfr_denref(m_val), k); mpfr_canonicalize(m_val); return *this; }

    friend mpfp operator+(mpfp a, mpfp const & b) { return a += b; }
    // friend mpfp operator+(mpfp a, mpz const & b) { return a += b; }
    // friend mpfp operator+(mpfp a, unsigned b)  { return a += b; }
    // friend mpfp operator+(mpfp a, int b)  { return a += b; }
    // friend mpfp operator+(mpz const & a, mpfp b) { return b += a; }
    // friend mpfp operator+(unsigned a, mpfp b) { return b += a; }
    // friend mpfp operator+(int a, mpfp b) { return b += a; }

    friend mpfp operator-(mpfp a, mpfp const & b) { return a -= b; }
    // friend mpfp operator-(mpfp a, mpz const & b) { return a -= b; }
    // friend mpfp operator-(mpfp a, unsigned b) { return a -= b; }
    // friend mpfp operator-(mpfp a, int b) { return a -= b; }
    // friend mpfp operator-(mpz const & a, mpfp b) { b.neg(); return b += a; }
    // friend mpfp operator-(unsigned a, mpfp b) { b.neg(); return b += a; }
    // friend mpfp operator-(int a, mpfp b) { b.neg(); return b += a; }

    friend mpfp operator*(mpfp a, mpfp const & b) { return a *= b; }
    // friend mpfp operator*(mpfp a, mpz const & b) { return a *= b; }
    // friend mpfp operator*(mpfp a, unsigned b) { return a *= b; }
    // friend mpfp operator*(mpfp a, int b) { return a *= b; }
    // friend mpfp operator*(mpz const & a, mpfp b) { return b *= a; }
    // friend mpfp operator*(unsigned a, mpfp b) { return b *= a; }
    // friend mpfp operator*(int a, mpfp b) { return b *= a; }

    friend mpfp operator/(mpfp a, mpfp const & b) { return a /= b; }
    // friend mpfp operator/(mpfp a, mpz const & b) { return a /= b; }
    // friend mpfp operator/(mpfp a, unsigned b) { return a /= b; }
    // friend mpfp operator/(mpfp a, int b) { return a /= b; }
    // friend mpfp operator/(mpz const & a, mpfp b) { b.inv(); return b *= a; }
    // friend mpfp operator/(unsigned a, mpfp b) { b.inv(); return b *= a; }
    // friend mpfp operator/(int a, mpfp b) { b.inv(); return b *= a; }

    // mpfp & operator++() { return operator+=(1); }
    // mpfp operator++(int) { mpfp r(*this); ++(*this); return r; }

    // mpfp & operator--() { return operator-=(1); }
    // mpfp operator--(int) { mpfp r(*this); --(*this); return r; }

    // void floor();
    // friend mpz floor(mpfp const & a);

    // void ceil();
    // friend mpz ceil(mpfp const & a);

    // friend void power(mpfp & a, mpfp const & b, unsigned k);
    // friend void _power(mpfp & a, mpfp const & b, unsigned k) { power(a, b, k); }
    // friend mpfp power(mpfp a, unsigned k) { power(a, a, k); return a; }

    friend std::ostream & operator<<(std::ostream & out, mpfp const & v);

    // friend void display_decimal(std::ostream & out, mpfp const & a, unsigned prec);

    // class decimal {
    //     mpfp const & m_val;
    //     unsigned     m_prec;
    // public:
    //     decimal(mpfp const & val, unsigned prec = 10):m_val(val), m_prec(prec) {}
    //     friend std::ostream & operator<<(std::ostream & out, decimal const & d) { display_decimal(out, d.m_val, d.m_prec); return out; }
    // };

};

template<>
class numeric_traits<mpfp> {
public:
    static bool precise() { return true; }
    static bool is_zero(mpfp const &  v) { return v.is_zero(); }
    static bool is_pos(mpfp const & v) { return v.is_pos(); }
    static bool is_neg(mpfp const & v) { return v.is_neg(); }
    static void set_rounding(bool plus_inf) {}
    static void neg(mpfp & v) { v.neg(); }
//    static void inv(mpfp & v) { v.inv(); }
//    static void reset(mpfp & v) { v = 0; }
    // v <- v^k
//    static void power(mpfp & v, unsigned k) { _power(v, v, k); }
};
}
