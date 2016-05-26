/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <random>
#include <vector>
#include "util/test.h"
#include "util/parray.h"
using namespace lean;

static void tst1() {
    parray<unsigned> a;
    lean_assert(a.size() == 0);
    a.push_back(10);
    parray<unsigned> a1 = a;
    a.push_back(20);
    a.push_back(30);
    lean_assert(a[0] == 10);
    lean_assert(a[1] == 20);
    a.set(1, 100);
    lean_assert(a[1] == 100);
    lean_assert(a.size() == 3);
    a.pop_back();
    a.display_internal(std::cout);
    lean_assert(a.size() == 2);
    a.compress();
    lean_assert(a[0] == 10);
    lean_assert(a[1] == 100);
    a.display_internal(std::cout);
}

static void driver(unsigned max_sz, unsigned max_val, unsigned num_it,
                   double push_back_freq,
                   double pop_back_freq,
                   double set_freq,
                   double copy_freq,
                   double compress_freq) {
    parray<unsigned> v1;
    std::vector<unsigned> v2;
    std::mt19937   rng;
    rng.seed(static_cast<unsigned int>(time(0)));
    std::uniform_int_distribution<unsigned int> uint_dist;
    std::vector<parray<unsigned>> copies;
    size_t acc_sz = 0;
    size_t compressed_counter = 0;
    for (unsigned i = 0; i < num_it; i++) {
        if (v1.is_compressed())
            compressed_counter++;
        acc_sz += v1.size();
        double f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < copy_freq) {
            copies.push_back(v1);
        }
        f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < push_back_freq) {
            if (v1.size() < max_sz) {
                unsigned a = uint_dist(rng) % max_val;
                v1.push_back(a);
                v2.push_back(a);
            }
        }
        if (v1.size() > 0) {
            f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
            if (f < pop_back_freq) {
                if (v1.size() >= max_sz)
                    continue;
                v1.pop_back();
                v2.pop_back();
            }
        }
        if (v1.size() > 0) {
            f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
            if (f < set_freq) {
                unsigned idx = uint_dist(rng) % v1.size();
                unsigned a   = uint_dist(rng) % max_val;
                v1.set(idx, a);
                v2[idx] = a;
            }
        }
        f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < compress_freq)
            v1.compress();
        lean_assert(v1.size() == v2.size());
        for (unsigned i = 0; i < v2.size(); i++) {
            lean_assert(v1[i] == v2[i]);
        }
    }
    std::cout << "\n";
    std::cout << "Copies created:  " << copies.size() << "\n";
    std::cout << "Average size:    " << static_cast<double>(acc_sz) / static_cast<double>(num_it) << "\n";
    std::cout << "Compressed freq: " << static_cast<double>(compressed_counter) * 100.0 / static_cast<double>(num_it) << "\n";
}

static void tst2() {
    driver(4,  32, 10000, 0.5, 0.1, 0.5, 0.1, 0.0);
    driver(4,  32, 10000, 0.5, 0.1, 0.5, 0.1, 0.1);
    driver(4,  32, 10000, 0.5, 0.1, 0.5, 0.5, 0.0);
    driver(16, 16, 100000, 0.5, 0.5, 0.5, 0.01, 0.0);
    driver(16, 16, 100000, 0.5, 0.1, 0.5, 0.01, 0.01);
    driver(16, 16, 100000, 0.5, 0.6, 0.5, 0.01, 0.0);
    driver(16, 16, 10000, 0.5, 0.1, 0.5, 0.0, 0.0);
}

static void tst3(unsigned n) {
    parray<unsigned> v1;
    v1.push_back(0);
    parray<unsigned> v2 = v1;
    for (unsigned i = 0; i < n; i++)
        v1.push_back(i);
    unsigned r = 0;
    for (unsigned i = 0; i < n; i++)
        r += v1.read(n - i - 1, 1000);
    std::cout << ">> " << r << "\n";
}

int main() {
    tst1();
    tst2();
    tst3(100000);
    return has_violations() ? 1 : 0;
}
