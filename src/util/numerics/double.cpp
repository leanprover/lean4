/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cmath>
#include "util/numerics/numeric_traits.h"
#include "util/numerics/double.h"

namespace lean {

static thread_local mpfr_rnd_t g_rnd;
void set_double_rnd(bool plus_inf) {
    g_rnd = plus_inf ? MPFR_RNDU : MPFR_RNDD;
}

mpfr_rnd_t get_double_rnd() {
    return g_rnd;
}

void double_power(double & v, unsigned k) { v = std::pow(v, k); }
void double_abs(double & v)   { v = std::abs(v); }
void double_ceil(double & v)  { v = std::ceil(v); }
void double_floor(double & v) { v = std::floor(v); }


};
