/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cmath>
#include "util/thread.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/float.h"

namespace lean {
void float_power(float & v, unsigned k) { v = std::pow(v, k); }
void float_abs(float & v)   { v = std::abs(v); }
void float_ceil(float & v)  { v = std::ceil(v); }
void float_floor(float & v) { v = std::floor(v); }

static float g_zero = 0.0;
float const & numeric_traits<float>::zero() {
    return g_zero;
}

static float g_one = 1.0;
float const & numeric_traits<float>::one() {
    return g_one;
}
};
