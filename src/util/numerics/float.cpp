/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "numeric_traits.h"
#include "float.h"
#include <cmath>

namespace lean {

thread_local mpfr_rnd_t numeric_traits<float>::rnd = MPFR_RNDN;

void float_power(float & v, unsigned k) { v = std::pow(v, k); }
void float_abs(float & v)   { v = std::abs(v); }
void float_ceil(float & v)  { v = std::ceil(v); }
void float_floor(float & v) { v = std::floor(v); }

};
