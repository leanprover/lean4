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

void float_power(double & v, unsigned k) {
    v = std::pow(v, k);
}
};
