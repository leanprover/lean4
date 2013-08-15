/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "numeric_traits.h"
#include "float.h"
#include <cmath>

namespace lean {

static thread_local mpfr_rnd_t g_rnd;
void set_float_rnd(bool plus_inf) {
    g_rnd = plus_inf ? MPFR_RNDU : MPFR_RNDD;
}

mpfr_rnd_t get_float_rnd() {
    return g_rnd;
}

void float_power(float & v, unsigned k) { v = std::pow(v, k); }
void float_abs(float & v)   { v = std::abs(v); }
void float_ceil(float & v)  { v = std::ceil(v); }
void float_floor(float & v) { v = std::floor(v); }

};
