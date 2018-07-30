/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <random>
#include <vector>
#include <functional>
#include <unordered_set>
#include "util/test.h"
#include "util/timeit.h"
#include "util/init_module.h"
#include "util/rb_map.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/phashtable.h"
#include "library/phash_map.h"
using namespace lean;

typedef phashtable<unsigned, std::hash<unsigned>, std::equal_to<unsigned>, true> unsigned_set;
typedef std::unordered_set<unsigned, std::hash<unsigned>> std_unsigned_set;

void tst1() {
    unsigned_set s;
    lean_assert(s.size() == 0);
    s.insert(10);
    s.for_each([](unsigned v) {
            lean_assert(v == 10);
        });
    lean_assert(s.contains(10));
    lean_assert(!s.contains(20));
    lean_assert(s.find(10));
    auto v = s.find(10);
    lean_assert(v && *v == 10);
    lean_assert(!s.find(20));
    s.erase(20);
    lean_assert(s.check_invariant());
    lean_assert(s.contains(10));
    s.erase(10);
    lean_assert(!s.contains(10));
    lean_assert(s.check_invariant());
}

static void tst2() {
    std::uniform_int_distribution<unsigned int> uint_dist;
    std::mt19937   rng;
    rng.seed(static_cast<unsigned int>(time(0)));
    const unsigned N = 10000;
    unsigned vals[N];
    unsigned_set s1;
    for (unsigned i = 1; i < N; i ++) {
        unsigned v = uint_dist(rng) % (N / 2);
        s1.insert(v);
        vals[i] = v;
        lean_assert(s1.contains(v));
    }
    std::cout << "step1\n"; std::cout.flush();
    for (unsigned i = 1; i < N; i ++) {
        lean_assert(s1.contains(vals[i]));
    }
    std::cout << "step2\n"; std::cout.flush();
    for (unsigned i = 1; i < N; i += 2) {
        s1.erase(vals[i]);
        lean_assert(!s1.contains(vals[i]));
    }
    std::cout << "step3\n"; std::cout.flush();
    for (unsigned i = 1; i < N; i += 2) {
        s1.insert(vals[i]);
    }
    std::cout << "step4\n"; std::cout.flush();
    for (unsigned i = 1; i < N; i ++) {
        lean_assert(s1.contains(vals[i]));
    }
}

static void tst3() {
    std::uniform_int_distribution<unsigned int> uint_dist;
    std::mt19937   rng;
    rng.seed(static_cast<unsigned int>(time(0)));
    unsigned_set     s1;
    std_unsigned_set s2;
    unsigned N = uint_dist(rng) % 1000;
    for (unsigned i = 0; i < N; i++) {
        unsigned v = uint_dist(rng)%1000;
        if (uint_dist(rng) % 3 == 2) {
            s1.erase(v);
            s2.erase(v);
            lean_assert(!s1.contains(v));
        } else {
            s1.insert(v);
            s2.insert(v);
            lean_assert(s1.contains(v));
        }
    }
    {
        std_unsigned_set::iterator it  = s2.begin();
        std_unsigned_set::iterator end = s2.end();
        for (; it != end; ++it) {
            lean_assert(s1.contains(*it));
        }
    }
    {
        unsigned n = 0;
        s1.for_each([&](unsigned v) {
                lean_assert(s2.find(v) != s2.end());
                n++;
            });
        lean_assert(n == s1.size());
    }
    lean_assert(s1.size() == s2.size());
}

static void tst4() {
    unsigned_set s1;
    s1.insert(10);
    s1.insert(20);
    unsigned_set s2 = s1;
    lean_assert(s2.contains(10));
    lean_assert(s2.contains(20));
    lean_assert(!s2.contains(30));
    s2.insert(30);
    lean_assert(s2.contains(30));
    lean_assert(!s1.contains(30));
}

static void tst5() {
    /* This example would take a few minute if we use std_unsigned_set.
       With unsigned_set, it takes a few milliseconds. */
    timeit timer(std::cout, "tst5");
    unsigned_set s1;
    for (unsigned i = 0; i < 100000; i++) {
        s1.insert(i);
    }
    for (unsigned i = 0; i < 100000; i++) {
        unsigned_set s2 = s1;
        s2.insert(99999999);
        lean_assert(s2.contains(10));
        lean_assert(s2.contains(99999999));
    }
    lean_assert(!s1.contains(99999999));
}

typedef phash_map<unsigned, unsigned, std::hash<unsigned>, std::equal_to<unsigned>, true> umap;

static void tst6() {
    umap m;
    m.insert(1, 2);
    lean_assert(m.contains(1));
    lean_assert(m.find(1) == optional<unsigned>(2));
    m.insert(1, 3);
    lean_assert(m.contains(1));
    lean_assert(m.find(1) == optional<unsigned>(3));
    lean_assert(m.contains(1));
    m.insert(2, 4);
    m.for_each([](unsigned k, unsigned v) {
            lean_assert(k == 1 || k == 2);
            lean_assert(v == 3 || v == 4);
        });
    lean_assert(m.size() == 2);
    lean_assert(m.contains(2));
    lean_assert(m.contains(1));
    m.erase(1);
    lean_assert(!m.contains(1));
    lean_assert(m.find(2) == optional<unsigned>(4));
    lean_assert(m.size() == 1);
}

void tst7(unsigned num, unsigned seed) {
    timeit t(std::cout, "phash_map + finalization");
    umap m;
    {
        timeit t(std::cout, "phash_map");
        std::mt19937   rng;
        rng.seed(seed);
        std::uniform_int_distribution<unsigned int> uint_dist;
        for (unsigned i = 0; i < num; i++) {
            m.insert(uint_dist(rng), uint_dist(rng));
        }
    }
}

void tst8(unsigned num, unsigned seed) {
    timeit t(std::cout, "phash_map with trail and num/100 snapshots + finalization");
    umap m;
    std::vector<umap> snapshots;
    {
        timeit t(std::cout, "phash_map with trail and num/100 snapshots");
        std::mt19937   rng;
        rng.seed(seed);
        std::uniform_int_distribution<unsigned int> uint_dist;
        for (unsigned k = 0; k < 100; k++) {
            snapshots.push_back(m);
            for (unsigned i = 0; i < num / 100; i++) {
                m.insert(uint_dist(rng), uint_dist(rng));
            }
        }
    }
}

void tst9(unsigned num, unsigned seed) {
    timeit t(std::cout, "phash_map with trail and 1 snapshot + finalization");
    umap m;
    {
        timeit t(std::cout, "phash_map with trail and 1 snapshot");
        std::mt19937   rng;
        rng.seed(seed);
        std::uniform_int_distribution<unsigned int> uint_dist;
        m.insert(uint_dist(rng), uint_dist(rng));
        umap m2 = m;
        for (unsigned i = 1; i < num; i++) {
            m.insert(uint_dist(rng), uint_dist(rng));
        }
    }
}

void tst10(unsigned num, unsigned seed) {
    timeit t(std::cout, "rb_map + finalization");
    unsigned_map<unsigned> m;
    {
        timeit t(std::cout, "rb_map");
        std::mt19937   rng;
        rng.seed(seed);
        std::uniform_int_distribution<unsigned int> uint_dist;
        for (unsigned i = 0; i < num; i++) {
            m.insert(uint_dist(rng), uint_dist(rng));
        }
    }
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_core_module();
    initialize_library_module();

    tst1();
    tst2();
    for (int i = 0; i < 1000; i++)
        tst3();
    tst4();
    tst5();
    tst6();
#if 0
    tst7(10000000, 2);
    tst8(10000000, 2);
    tst9(10000000, 2);
    tst10(10000000, 2);
#endif
    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
