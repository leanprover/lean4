/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cmath>
#include "util/thread.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/double.h"

namespace lean {
void double_power(double & v, unsigned k) { v = std::pow(v, k); }
void double_abs(double & v)   { v = std::abs(v); }
void double_ceil(double & v)  { v = std::ceil(v); }
void double_floor(double & v) { v = std::floor(v); }

double numeric_traits<double>::g_zero = 0.0;
double numeric_traits<double>::g_one = 1.0;

double numeric_traits<double>::log(double d) {
    return std::log(d);
}
};
