/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/debug.h"

namespace lean {
/**
   \brief Template for computing GCD using binary method
*/
template<typename T>
static T gcd(T u, T v) {
    if (u == 0)
        return v;
    if (v == 0)
        return u;

    int k;

    for (k = 0; ((u | v) & 1) == 0; ++k) {
        u >>= 1;
        v >>= 1;
    }

    while ((u & 1) == 0)
        u >>= 1;

    do {
        while ((v & 1) == 0)
            v >>= 1;

        if (u < v) {
            v -= u;
        } else {
            T diff = u - v;
            u = v;
            v = diff;
        }
        v >>= 1;
    } while (v != 0);

    return u << k;
}

/**
   \brief Template for the extended GCD procedure
*/
template<typename T>
void gcdext(T & r, T & a, T & b, T const & r1, T const & r2) {
    using std::swap;
    T aux, quot;
    T tmp1 = r1;
    T tmp2 = r2;
    a = 1;
    b = 0;
    T next_a, next_b;
    next_a = 0;
    next_b = 1;
    if (tmp1 < 0) tmp1 = -tmp1;
    if (tmp2 < 0) tmp2 = -tmp2;

    if (tmp1 < tmp2) {
        swap(tmp1, tmp2);
        swap(next_a, next_b);
        swap(a, b);
    }

    // tmp1 >= tmp2 >= 0
    // quot_rem in one function would be faster.
    while (tmp2 > 0) {
        lean_assert(tmp1 >= tmp2);
        aux    = tmp2;
        quot   = tmp1 / tmp2;
        tmp2   = tmp1 % tmp2;
        tmp1   = aux;
        aux    = next_a;
        next_a = a - (quot * next_a);
        a      = aux;
        aux    = next_b;
        next_b = b - (quot * next_b);
        b      = aux;
    }

    if (r1 < 0) a = -a;
    if (r2 < 0) b = -b;
    r = tmp1;
}
}
