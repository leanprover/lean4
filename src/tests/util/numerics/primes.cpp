/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "util/init_module.h"
#include "util/numerics/primes.h"
#include "util/numerics/init_module.h"
using namespace lean;

#define NUM_SMALL_PRIMES 168
static uint64 small_primes[NUM_SMALL_PRIMES] = {
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997
};

static void tst1() {
    prime_iterator it;
    for (unsigned i = 0; i < NUM_SMALL_PRIMES; i++) {
        uint64 p = it.next();
        lean_assert_eq(p, small_primes[i]);
        std::cout << p << " ";
    }
    std::cout << "\n";
}

static void tst2() {
    prime_iterator it;
    for (unsigned i = 0; i < 100000; i++) {
        uint64 p = it.next();
        lean_assert(is_prime(p));
        if (i % 1000 == 0)
            std::cout << p << " "; std::cout.flush();
    }
    std::cout << "\n";
}

int main() {
    initialize_util_module();
    initialize_numerics_module();
    tst1();
    tst2();
    finalize_numerics_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
