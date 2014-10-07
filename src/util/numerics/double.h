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
void double_power(double & v, unsigned k);
void double_abs(double & v);
void double_ceil(double & v);
void double_floor(double & v);

// Macro to implement transcendental functions using MPFR
#define LEAN_TRANS_DOUBLE_FUNC(f, v, rnd)       \
    mpfp t(53);                                 \
    t = v;                                      \
    t.f(rnd);                                   \
    v = t.get_double(rnd);

void set_double_rnd(bool plus_inf);
mpfr_rnd_t get_double_rnd();

template<>
class numeric_traits<double> {
public:
    static bool precise() { return false; }
    static bool is_zero(double v) { return v == 0.0; }
    static bool is_pos(double v) { return v > 0.0; }
    static bool is_neg(double v) { return v < 0.0; }
    static mpfr_rnd_t rnd() { return get_double_rnd(); }
    static void set_rounding(bool plus_inf) { set_double_rnd(plus_inf); }
    static void neg(double & v) { v = -v; }
    static void inv(double & v) { v = 1.0/v; }
    static void reset(double & v) { v = 0.0; }
    static double const & zero();

    static void power(double & v, unsigned k) { double_power(v, k); }
    static void abs(double & v) { double_abs(v); }
    static void ceil(double & v) { double_ceil(v); }
    static void floor(double & v) { double_floor(v); }
    static double const & min(double const & v1, double const & v2) {
        return v1 < v2 ? v1 : v2;
    }
    static double const & max(double const & v1, double const & v2) {
        return v1 > v2 ? v1 : v2;
    }

    // constants
    static const  double constexpr pi_l = (3373259426.0 + 273688.0 / (1<<21)) / (1<<30);
    static const  double constexpr pi_n = (3373259426.0 + 273688.0 / (1<<21)) / (1<<30);
    static const  double constexpr pi_u = (3373259426.0 + 273689.0 / (1<<21)) / (1<<30);
    static inline double pi_lower()       { return pi_l;     }
    static inline double pi()             { return pi_n;     }
    static inline double pi_upper()       { return pi_u;     }
    static inline double pi_half_lower()  { return pi_l / 2; }
    static inline double pi_half()        { return pi_n / 2; }
    static inline double pi_half_upper()  { return pi_u / 2; }
    static inline double pi_twice_lower() { return pi_l * 2; }
    static inline double pi_twice()       { return pi_n * 2; }
    static inline double pi_twice_upper() { return pi_u * 2; }

    // Transcendental functions using MPFR
    static void exp(double & v)   { LEAN_TRANS_DOUBLE_FUNC(exp,   v, rnd()); }
    static void exp2(double & v)  { LEAN_TRANS_DOUBLE_FUNC(exp2,  v, rnd()); }
    static void exp10(double & v) { LEAN_TRANS_DOUBLE_FUNC(exp10, v, rnd()); }
    static void log(double & v)   { LEAN_TRANS_DOUBLE_FUNC(log,   v, rnd()); }
    static void log2(double & v)  { LEAN_TRANS_DOUBLE_FUNC(log2,  v, rnd()); }
    static void log10(double & v) { LEAN_TRANS_DOUBLE_FUNC(log10, v, rnd()); }
    static void sin(double & v)   { LEAN_TRANS_DOUBLE_FUNC(sin,   v, rnd()); }
    static void cos(double & v)   { LEAN_TRANS_DOUBLE_FUNC(cos,   v, rnd()); }
    static void tan(double & v)   { LEAN_TRANS_DOUBLE_FUNC(tan,   v, rnd()); }
    static void sec(double & v)   { LEAN_TRANS_DOUBLE_FUNC(sec,   v, rnd()); }
    static void csc(double & v)   { LEAN_TRANS_DOUBLE_FUNC(csc,   v, rnd()); }
    static void cot(double & v)   { LEAN_TRANS_DOUBLE_FUNC(cot,   v, rnd()); }
    static void asin(double & v)  { LEAN_TRANS_DOUBLE_FUNC(asin,  v, rnd()); }
    static void acos(double & v)  { LEAN_TRANS_DOUBLE_FUNC(acos,  v, rnd()); }
    static void atan(double & v)  { LEAN_TRANS_DOUBLE_FUNC(atan,  v, rnd()); }
    static void sinh(double & v)  { LEAN_TRANS_DOUBLE_FUNC(sinh,  v, rnd()); }
    static void cosh(double & v)  { LEAN_TRANS_DOUBLE_FUNC(cosh,  v, rnd()); }
    static void tanh(double & v)  { LEAN_TRANS_DOUBLE_FUNC(tanh,  v, rnd()); }
    static void asinh(double & v) { LEAN_TRANS_DOUBLE_FUNC(asinh, v, rnd()); }
    static void acosh(double & v) { LEAN_TRANS_DOUBLE_FUNC(acosh, v, rnd()); }
    static void atanh(double & v) { LEAN_TRANS_DOUBLE_FUNC(atanh, v, rnd()); }
};
}
