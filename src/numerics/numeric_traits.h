/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#pragma once

namespace lean {

template<typename T>
class numeric_traits {
};

void set_processor_rounding(bool plus_inf);
void double_power(double & v, unsigned k);

template<>
class numeric_traits<double> {
public:
    static bool is_zero(double v) { return v == 0.0; }
    static bool is_pos(double v) { return v > 0.0; }
    static bool is_neg(double v) { return v < 0.0; }
    static void set_rounding(bool plus_inf) { set_processor_rounding(plus_inf); }
    static void neg(double & v) { v = -v; }
    static void inv(double & v) { v = 1.0/v; }
    static void reset(double & v) { v = 0.0; }
    // b <- b^k
    static void power(double & v, unsigned k) { double_power(v, k); }
};

}
