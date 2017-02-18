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
void float_power(float & v, unsigned k);
void float_abs(float & v);
void float_ceil(float & v);
void float_floor(float & v);

template<>
class numeric_traits<float> {
public:
    static bool precise() { return false; }
    static bool is_zero(float v) { return v == 0.0; }
    static bool is_pos(float v) { return v > 0.0; }
    static bool is_neg(float v) { return v < 0.0; }
    static void neg(float & v) { v = -v; }
    static void inv(float & v) { v = 1.0/v; }
    static void reset(float & v) { v = 0.0; }
    static float const & zero();
    static float const & one();

    static void power(float & v, unsigned k) { float_power(v, k); }
    static void abs(float & v) { float_abs(v); }
    static void ceil(float & v) { float_ceil(v); }
    static void floor(float & v) { float_floor(v); }
    static double get_double(float const & d) { return static_cast<double>(d); }

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
};
}
