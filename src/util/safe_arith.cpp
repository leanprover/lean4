/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "util/exception.h"

namespace lean {
void check_int_overflow(long long n) {
    static_assert(sizeof(n) > sizeof(int), // NOLINT
                  "sizeof(long long) is not bigger than sizeof(int).");
    if (n < std::numeric_limits<int>::min())
        throw exception("integer underflow");
    if (n > std::numeric_limits<int>::max())
        throw exception("integer overflow");
}

template<typename Num>
int safe_sub_core(int v, Num k) {
    long long r = static_cast<long long>(v) - static_cast<long long>(k);
    check_int_overflow(r);
    return static_cast<int>(r);
}
int safe_sub(int v, int k) { return safe_sub_core(v, k); }
int safe_sub(int v, unsigned k) { return safe_sub_core(v, k); }

template<typename Num1, typename Num2>
Num1 safe_add_core(Num1 v, Num2 k) {
    long long r = static_cast<long long>(v) + static_cast<long long>(k);
    check_int_overflow(r);
    return static_cast<Num1>(r);
}
int safe_add(int v, int k) { return safe_add_core(v, k); }
int safe_add(int v, unsigned k) { return safe_add_core(v, k); }
unsigned safe_add(unsigned v, unsigned k) { return safe_add_core(v, k); }
}
