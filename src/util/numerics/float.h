/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <cstddef>
#include <mpfr.h>
#include "util/numerics/mpfp.h"

namespace lean {

/**
   \brief Template specializations define traits for native and lean
   numeric types.
*/
void float_power(float & v, unsigned k);
void float_abs(float & v);
void float_ceil(float & v);
void float_floor(float & v);

// Macro to implement transcendental functions using MPFR
#define LEAN_TRANS_FLOAT_FUNC(f, v, rnd)        \
    mpfp t(24);                                 \
    t = v;                                      \
    t.f(rnd);                                   \
    v = t.get_float(rnd);

void set_float_rnd(bool plus_inf);
mpfr_rnd_t get_float_rnd();

template<>
class numeric_traits<float> {
public:
    static bool precise() { return false; }
    static bool is_zero(float v) { return v == 0.0; }
    static bool is_pos(float v) { return v > 0.0; }
    static bool is_neg(float v) { return v < 0.0; }
    static mpfr_rnd_t rnd() { return get_float_rnd(); }
    static void set_rounding(bool plus_inf) { set_float_rnd(plus_inf); }
    static void neg(float & v) { v = -v; }
    static void inv(float & v) { v = 1.0/v; }
    static void reset(float & v) { v = 0.0; }
    static float const & zero();

    static void power(float & v, unsigned k) { float_power(v, k); }
    static void abs(float & v) { float_abs(v); }
    static void ceil(float & v) { float_ceil(v); }
    static void floor(float & v) { float_floor(v); }

    static float const & min(float const & v1, float const & v2) {
        return v1 < v2 ? v1 : v2;
    }
    static float const & max(float const & v1, float const & v2) {
        return v1 > v2 ? v1 : v2;
    }

    // constants
    static const  float constexpr pi_l = 13176794.0f/(1<<22);
    static const  float constexpr pi_n = 13176795.0f/(1<<22);
    static const  float constexpr pi_u = 13176795.0f/(1<<22);
    static inline float pi_lower()       { return pi_l;     }
    static inline float pi()             { return pi_n;     }
    static inline float pi_upper()       { return pi_u;     }
    static inline float pi_half_lower()  { return pi_l / 2; }
    static inline float pi_half()        { return pi_n / 2; }
    static inline float pi_half_upper()  { return pi_u / 2; }
    static inline float pi_twice_lower() { return pi_l * 2; }
    static inline float pi_twice()       { return pi_n * 2; }
    static inline float pi_twice_upper() { return pi_u * 2; }

    // Transcendental functions using MPFR
    static void exp(float & v)   { LEAN_TRANS_FLOAT_FUNC(exp,   v, rnd()); }
    static void exp2(float & v)  { LEAN_TRANS_FLOAT_FUNC(exp2,  v, rnd()); }
    static void exp10(float & v) { LEAN_TRANS_FLOAT_FUNC(exp10, v, rnd()); }
    static void log(float & v)   { LEAN_TRANS_FLOAT_FUNC(log,   v, rnd()); }
    static void log2(float & v)  { LEAN_TRANS_FLOAT_FUNC(log2,  v, rnd()); }
    static void log10(float & v) { LEAN_TRANS_FLOAT_FUNC(log10, v, rnd()); }
    static void sin(float & v)   { LEAN_TRANS_FLOAT_FUNC(sin,   v, rnd()); }
    static void cos(float & v)   { LEAN_TRANS_FLOAT_FUNC(cos,   v, rnd()); }
    static void tan(float & v)   { LEAN_TRANS_FLOAT_FUNC(tan,   v, rnd()); }
    static void sec(float & v)   { LEAN_TRANS_FLOAT_FUNC(sec,   v, rnd()); }
    static void csc(float & v)   { LEAN_TRANS_FLOAT_FUNC(csc,   v, rnd()); }
    static void cot(float & v)   { LEAN_TRANS_FLOAT_FUNC(cot,   v, rnd()); }
    static void asin(float & v)  { LEAN_TRANS_FLOAT_FUNC(asin,  v, rnd()); }
    static void acos(float & v)  { LEAN_TRANS_FLOAT_FUNC(acos,  v, rnd()); }
    static void atan(float & v)  { LEAN_TRANS_FLOAT_FUNC(atan,  v, rnd()); }
    static void sinh(float & v)  { LEAN_TRANS_FLOAT_FUNC(sinh,  v, rnd()); }
    static void cosh(float & v)  { LEAN_TRANS_FLOAT_FUNC(cosh,  v, rnd()); }
    static void tanh(float & v)  { LEAN_TRANS_FLOAT_FUNC(tanh,  v, rnd()); }
    static void asinh(float & v) { LEAN_TRANS_FLOAT_FUNC(asinh, v, rnd()); }
    static void acosh(float & v) { LEAN_TRANS_FLOAT_FUNC(acosh, v, rnd()); }
    static void atanh(float & v) { LEAN_TRANS_FLOAT_FUNC(atanh, v, rnd()); }
};
}
