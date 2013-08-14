/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cmath>
#include "mpfp.h"

namespace lean {
static thread_local mpfr_rnd_t g_mpfp_rnd = MPFR_RNDN;

mpfp numeric_traits<mpfp>::pi_l;
mpfp numeric_traits<mpfp>::pi_n;
mpfp numeric_traits<mpfp>::pi_u;

void set_mpfp_rnd(bool plus_inf) {
    g_mpfp_rnd = plus_inf ? MPFR_RNDU : MPFR_RNDD;
}

mpfr_rnd_t get_mpfp_rnd() {
    return g_mpfp_rnd;
}

/**
    \brief Auxiliary class for invoking mpfr_free_cache before
    exiting and avoiding Valgrind memory leak warnings.
*/
class mpfr_finalizer {
public:
    ~mpfr_finalizer() { mpfr_free_cache(); }
};
static mpfr_finalizer g_mpfr_finalizer;

inline unsigned necessary_digits(mpfr_prec_t p) {
    static constexpr double LOG10_2 = 0.30102999566;
    return std::ceil(p * LOG10_2) + 2;
}

std::ostream & operator<<(std::ostream & out, mpfp const & v) {
    char * s = nullptr;
    char format[128];
    sprintf(format, "%%.%dRNg", necessary_digits(mpfr_get_prec(v.m_val)));
    mpfr_asprintf(&s, format, v.m_val);
    std::string str = std::string(s);
    mpfr_free_str(s);
    out << str;
    return out;
}
}

void print(lean::mpfp const & v) { std::cout << v << std::endl; }
