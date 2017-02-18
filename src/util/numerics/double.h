/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <cstddef>
#include "util/numerics/numeric_traits.h"

namespace lean {
/**
   \brief Template specializations define traits for native and lean
   numeric types.
*/
void double_power(double & v, unsigned k);
void double_abs(double & v);
void double_ceil(double & v);
void double_floor(double & v);

template<>
class numeric_traits<double> {
public:
    static bool precise() { return false; }
    static bool is_zero(double v) { return v == 0.0; }
    static bool is_pos(double v) { return v > 0.0; }
    static bool is_neg(double v) { return v < 0.0; }
    static void neg(double & v) { v = -v; }
    static void inv(double & v) { v = 1.0/v; }
    static void reset(double & v) { v = 0.0; }
    static double g_zero;
    static double const & zero() { return g_zero; }
    static double g_one;
    static double const & one() { return g_one; }
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

    static double const & get_double(double const & d) { return d;}

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

    static double log(double d);
};
}
