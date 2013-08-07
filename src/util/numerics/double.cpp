/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "numeric_traits.h"
#include "double.h"
#include <cmath>

namespace lean {

mpfr_rnd_t numeric_traits<double>::rnd = MPFR_RNDN;

void double_power(double & v, unsigned k) {
    v = std::pow(v, k);
}
};
