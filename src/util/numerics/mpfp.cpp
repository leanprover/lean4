/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cmath>
#include "mpfp.h"

namespace lean {

inline unsigned necessary_digits(mpfr_prec_t p) {
    static constexpr double LOG10_2 = 0.30102999566;
    return std::ceil(p * LOG10_2) + 2;
}

std::ostream & operator<<(std::ostream & out, mpfp const & v) {
    static thread_local char* s = nullptr;
    static thread_local char format[128];
    sprintf(format, "%%.%dRNg", necessary_digits(mpfr_get_prec(v.m_val)));
    mpfr_asprintf(&s, format, v.m_val);
    std::string str = std::string(s);
    out << str;
    return out;
}
}

void print(lean::mpfp const & v) { std::cout << v << std::endl; }
