/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cmath>
#include <cstdio>
#include <string>
#include "util/thread.h"
#include "util/numerics/mpfp.h"

namespace lean {
MK_THREAD_LOCAL_GET(mpfr_rnd_t, get_g_mpfp_rnd, MPFR_RNDN);

void set_mpfp_rnd(bool plus_inf) {
    get_g_mpfp_rnd() = plus_inf ? MPFR_RNDU : MPFR_RNDD;
}

mpfr_rnd_t get_mpfp_rnd() {
    return get_g_mpfp_rnd();
}

inline unsigned necessary_digits(mpfr_prec_t p) {
    static constexpr double LOG10_2 = 0.30102999566;
    return std::ceil(p * LOG10_2) + 2;
}

std::ostream & operator<<(std::ostream & out, mpfp const & v) {
    char * s = nullptr;
    char format[128];
    sprintf(format, "%%.%dRNg", necessary_digits(mpfr_get_prec(v.m_val))); // NOLINT
    mpfr_asprintf(&s, format, v.m_val);
    std::string str = std::string(s);
    mpfr_free_str(s);
    out << str;
    return out;
}

static mpfp * g_zero = nullptr;
mpfp const & numeric_traits<mpfp>::zero() {
    lean_assert(is_zero(*g_zero));
    return *g_zero;
}

void initialize_mpfp() {
    g_zero = new mpfp(0.0);
}

void finalize_mpfp() {
    delete g_zero;
    mpfr_free_cache();
}
}
void print(lean::mpfp const & v) { std::cout << v << std::endl; }
