/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once
#include <mpfr.h>

namespace lean {

/**
   \brief Template specializations define traits for native and lean
   numeric types.
*/
template<typename T>
class numeric_traits {
};

void set_processor_rounding(bool plus_inf);
void double_power(double & v, unsigned k);
void float_power(float & v, unsigned k);

// Macro to implement transcendental functions using MPFR
#define LEAN_TRANS_FLOAT_FUNC(f, v) mpfr_t t;                  \
    mpfr_init2(t, 24); /* precision of float = 24bit */        \
    mpfr_set_flt(t, v, rnd);                                   \
    mpfr_##f(t, t, rnd);                                       \
    v = mpfr_get_flt(t, rnd);                                  \
    mpfr_clear (t);                                            \

// Macro to implement transcendental functions using MPFR
#define LEAN_TRANS_DOUBLE_FUNC(f, v) mpfr_t t;           \
    mpfr_init2(t, 53); /* precision of double = 53bit */ \
    mpfr_set_d(t, v, rnd);                               \
    mpfr_##f(t, t, rnd);                                 \
    v = mpfr_get_d(t, rnd);                              \
    mpfr_clear (t);                                      \

template<>
class numeric_traits<double> {
public:
    static mpfr_rnd_t rnd;
    static bool precise() { return false; }
    static bool is_zero(double v) { return v == 0.0; }
    static bool is_pos(double v) { return v > 0.0; }
    static bool is_neg(double v) { return v < 0.0; }
    static void set_rounding(bool plus_inf) { rnd = plus_inf ? MPFR_RNDU : MPFR_RNDD; }
    static void neg(double & v) { v = -v; }
    static void inv(double & v) { v = 1.0/v; }
    static void reset(double & v) { v = 0.0; }
    // v <- v^k
    static void power(double & v, unsigned k) { double_power(v, k); }

    // Transcendental functions using MPFR
    static void exp(double & v)   { LEAN_TRANS_DOUBLE_FUNC(exp,   v); }
    static void exp2(double & v)  { LEAN_TRANS_DOUBLE_FUNC(exp2,  v); }
    static void exp10(double & v) { LEAN_TRANS_DOUBLE_FUNC(exp10, v); }
    static void log(double & v)   { LEAN_TRANS_DOUBLE_FUNC(log,   v); }
    static void log2(double & v)  { LEAN_TRANS_DOUBLE_FUNC(log2,  v); }
    static void log10(double & v) { LEAN_TRANS_DOUBLE_FUNC(log10, v); }
    static void sin(double & v)   { LEAN_TRANS_DOUBLE_FUNC(sin,   v); }
    static void cos(double & v)   { LEAN_TRANS_DOUBLE_FUNC(cos,   v); }
    static void tan(double & v)   { LEAN_TRANS_DOUBLE_FUNC(tan,   v); }
    static void sec(double & v)   { LEAN_TRANS_DOUBLE_FUNC(sec,   v); }
    static void csc(double & v)   { LEAN_TRANS_DOUBLE_FUNC(csc,   v); }
    static void cot(double & v)   { LEAN_TRANS_DOUBLE_FUNC(cot,   v); }
    static void asin(double & v)  { LEAN_TRANS_DOUBLE_FUNC(asin,  v); }
    static void acos(double & v)  { LEAN_TRANS_DOUBLE_FUNC(acos,  v); }
    static void atan(double & v)  { LEAN_TRANS_DOUBLE_FUNC(atan,  v); }
    static void sinh(double & v)  { LEAN_TRANS_DOUBLE_FUNC(sinh,  v); }
    static void cosh(double & v)  { LEAN_TRANS_DOUBLE_FUNC(cosh,  v); }
    static void tanh(double & v)  { LEAN_TRANS_DOUBLE_FUNC(tanh,  v); }
    static void asinh(double & v) { LEAN_TRANS_DOUBLE_FUNC(asinh, v); }
    static void acosh(double & v) { LEAN_TRANS_DOUBLE_FUNC(acosh, v); }
    static void atanh(double & v) { LEAN_TRANS_DOUBLE_FUNC(atanh, v); }
};

template<>
class numeric_traits<float> {
public:
    static mpfr_rnd_t rnd;
    static bool precise() { return false; }
    static bool is_zero(float v) { return v == 0.0; }
    static bool is_pos(float v) { return v > 0.0; }
    static bool is_neg(float v) { return v < 0.0; }
    static void set_rounding(bool plus_inf) { rnd = plus_inf ? MPFR_RNDU : MPFR_RNDD; }
    static void neg(float & v) { v = -v; }
    static void inv(float & v) { v = 1.0/v; }
    static void reset(float & v) { v = 0.0; }
    // v <- v^k
    static void power(float & v, unsigned k) { float_power(v, k); }

    // Transcendental functions using MPFR
    static void exp(float & v)   { LEAN_TRANS_FLOAT_FUNC(exp,   v); }
    static void exp2(float & v)  { LEAN_TRANS_FLOAT_FUNC(exp2,  v); }
    static void exp10(float & v) { LEAN_TRANS_FLOAT_FUNC(exp10, v); }
    static void log(float & v)   { LEAN_TRANS_FLOAT_FUNC(log,   v); }
    static void log2(float & v)  { LEAN_TRANS_FLOAT_FUNC(log2,  v); }
    static void log10(float & v) { LEAN_TRANS_FLOAT_FUNC(log10, v); }
    static void sin(float & v)   { LEAN_TRANS_FLOAT_FUNC(sin,   v); }
    static void cos(float & v)   { LEAN_TRANS_FLOAT_FUNC(cos,   v); }
    static void tan(float & v)   { LEAN_TRANS_FLOAT_FUNC(tan,   v); }
    static void sec(float & v)   { LEAN_TRANS_FLOAT_FUNC(sec,   v); }
    static void csc(float & v)   { LEAN_TRANS_FLOAT_FUNC(csc,   v); }
    static void cot(float & v)   { LEAN_TRANS_FLOAT_FUNC(cot,   v); }
    static void asin(float & v)  { LEAN_TRANS_FLOAT_FUNC(asin,  v); }
    static void acos(float & v)  { LEAN_TRANS_FLOAT_FUNC(acos,  v); }
    static void atan(float & v)  { LEAN_TRANS_FLOAT_FUNC(atan,  v); }
    static void sinh(float & v)  { LEAN_TRANS_FLOAT_FUNC(sinh,  v); }
    static void cosh(float & v)  { LEAN_TRANS_FLOAT_FUNC(cosh,  v); }
    static void tanh(float & v)  { LEAN_TRANS_FLOAT_FUNC(tanh,  v); }
    static void asinh(float & v) { LEAN_TRANS_FLOAT_FUNC(asinh, v); }
    static void acosh(float & v) { LEAN_TRANS_FLOAT_FUNC(acosh, v); }
    static void atanh(float & v) { LEAN_TRANS_FLOAT_FUNC(atanh, v); }
};

}
