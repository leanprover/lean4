/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <cstdlib>
#include "test.h"
#include "pvector.h"
#include "timeit.h"
using namespace lean;

// #define PVECTOR_PERF_TEST

static void tst1() {
    pvector<int> v;
    lean_assert(v.empty());
    v.push_back(10);
    lean_assert(v.size() == 1);
    lean_assert(v.back() == 10);
    v.set(0, 20);
    lean_assert(v.back() == 20);
    v.pop_back();
    lean_assert(v.size() == 0);
    v.push_back(10);
    v.push_back(20);
    pvector<int> v2(v);
    lean_assert(v2.size() == 2);
    v2.push_back(30);
    lean_assert(v.size() == 2);
    lean_assert(v2.size() == 3);
    v2.pop_back();
    lean_assert(v.size() == 2);
    v2.set(1, 100);
    lean_assert(v[1] == 20);
    lean_assert(v2[1] == 100);
    for (unsigned i = 0; i < 100; i++)
        v2.push_back(i);
}

template<typename T>
bool operator==(pvector<T> v1, std::vector<T> const & v2) {
    if (v1.size() != v2.size())
        return false;
    for (unsigned i = 0; i < v1.size(); i++) {
        if (v1[i] != v2[i])
            return false;
    }
    return true;
}

template<typename T>
bool operator==(pvector<T> v1, pvector<T> v2) {
    if (v1.size() != v2.size())
        return false;
    for (unsigned i = 0; i < v1.size(); i++) {
        if (v1[i] != v2[i])
            return false;
    }
    return true;
}

static void driver(unsigned max_sz, unsigned max_val, unsigned num_ops, double updt_freq, double copy_freq) {
    std::vector<int> v1;
    pvector<int>     v2;
    pvector<int>     v3;
    std::vector<pvector<int>> copies;
    for (unsigned i = 0; i < num_ops; i++) {
        double f = static_cast<double>(std::rand() % 10000) / 10000.0;
        if (f < copy_freq) {
            copies.push_back(v2);
        }
        f = static_cast<double>(std::rand() % 10000) / 10000.0;
        // read random positions of v3
        if (!empty(v3)) {
            for (unsigned j = 0; j < rand() % 5; j++) {
                unsigned idx = rand() % size(v3);
                lean_assert(v3[idx] == v1[idx]);
            }
        }
        if (f < updt_freq) {
            if (v1.size() >= max_sz)
                continue;
            int a = std::rand() % max_val;
            if (!empty(v2) && rand()%2 == 0) {
                unsigned idx = rand() % size(v2);
                v1[idx] = a;
                v2[idx] = a;
                v3[idx] = a;
                lean_assert(v1[idx] == v2[idx]);
                lean_assert(v1[idx] == v3[idx]);
            } else {
                v1.push_back(a);
                v2.push_back(a);
                v3 = push_back(v3, a);
                lean_assert(back(v3) == a);
            }
        } else {
            if (v1.size() == 0)
                continue;
            lean_assert(v1.back() == v2.back());
            v1.pop_back();
            v2.pop_back();
            v3 = pop_back(v3);
        }
        lean_assert(v2 == v1);
        lean_assert(v3 == v1);
    }
    std::cout << "Copies created: " << copies.size() << "\n";
}

static void tst2() {
    driver(4,  32, 10000, 0.5, 0.01);
    driver(4,  32, 10000, 0.5, 0.1);
    driver(2,  32, 10000, 0.8, 0.4);
    driver(2,  32, 10000, 0.3, 0.5);
    driver(4,  32, 10000, 0.3, 0.7);
    driver(16, 32, 10000, 0.5, 0.1);
    driver(16, 32, 10000, 0.5, 0.01);
    driver(16, 32, 10000, 0.5, 0.5);
    driver(16, 32, 10000, 0.7, 0.1);
    driver(16, 32, 10000, 0.7, 0.5);
    driver(16, 32, 10000, 0.7, 0.01);
    driver(16, 32, 10000, 0.1, 0.5);
    driver(16, 32, 10000, 0.8, 0.2);
    driver(128, 1000, 10000, 0.5, 0.5);
    driver(128, 1000, 10000, 0.5, 0.01);
    driver(128, 1000, 10000, 0.5, 0.1);
    driver(128, 1000, 10000, 0.2, 0.5);
    driver(128, 1000, 10000, 0.2, 0.01);
    driver(128, 1000, 10000, 0.2, 0.1);
}

static void tst3() {
    timeit t(std::cout, "tst3");
    unsigned N = 20000;
    unsigned M = 20000;
    pvector<int> v;
    for (unsigned i = 0; i < N; i++) v.push_back(i);
    pvector<int> v2 = v;
    for (unsigned i = 0; i < N / 2; i++) v2.push_back(i);
    // v2 has a long trail of deltas
    // Now, we only read v2
    unsigned s = 0;
    for (unsigned i = 0; i < M; i++) { s += v2[i % v2.size()]; }
}

static void tst4() {
    pvector<int> v;
    lean_assert(empty(v));
    lean_assert(size(v) == 0);
    v = push_back(v, 1);
    lean_assert(size(v) == 1);
    std::cout << "v: " << v << "\n";
    lean_assert(back(v) == 1);
    lean_assert(!empty(v));
    v = push_back(v, 2);
    lean_assert(back(v) == 2);
    std::cout << "v: " << v << "\n";
    v = push_back(v, 3);
    std::cout << "v: " << v << "\n";
    lean_assert(size(v) == 3);
    lean_assert(v[0] == 1);
    lean_assert(back(v) == 3);
    lean_assert(size(pop_back(v)) == 2);
    lean_assert(back(pop_back(v)) == 2);
    lean_assert(pop_back(pop_back(v))[0] == 1);
    lean_assert(empty(pop_back(pop_back(pop_back(v)))));
    lean_assert(pop_back(push_back(v, 3)) == v);
}

static void tst5() {
    pvector<int> v;
    v.push_back(0);
    pvector<int> v2 = v;
    for (unsigned i = 1; i < 100; i++) {
        lean_assert(v2[0] == 0);
        v2.push_back(i);
        lean_assert(v2[0] == 0);
        v = pvector<int>();
    }
}

static void tst6() {
    pvector<int> v;
    v.push_back(0);
    v.push_back(1);
    pvector<int> v2 = v;
    v2[0] = 10;
    lean_assert(v2[0] == 10);
    lean_assert(v[0] == 0);
    v[0] = 5;
    lean_assert(v2[0] == 10);
    lean_assert(v[0] == 5);
    v2[1] = 20;
    lean_assert(v2[0] == 10);
    lean_assert(v2[1] == 20);
}

#ifdef PVECTOR_PERF_TEST
static void perf_vector(unsigned n) {
    std::vector<int> q;
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_back();
    }
}

static void perf_pvector(unsigned n) {
    pvector<int> q;
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_back();
    }
}

static void tst_perf1() {
    unsigned N = 100000;
    unsigned M = 100;
    {
        timeit t(std::cout, "vector time");
        for (unsigned i = 0; i < N; i++) perf_vector(M);
    }
    {
        timeit t(std::cout, "pvector time");
        for (unsigned i = 0; i < N; i++) perf_pvector(M);
    }
}

static void perf_vector2(std::vector<int> q, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_back();
    }
}

static void perf_pvector2(pvector<int> q, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_back();
    }
}

static void tst_perf2() {
    unsigned N = 100000;
    unsigned SZ1 = 10000;
    unsigned M   = 10;
    {
        timeit t(std::cout, "vector time");
        std::vector<int> q;
        for (unsigned i = 0; i < SZ1; i++) { q.push_back(i); }
        for (unsigned i = 0; i < N; i++) perf_vector2(q, M);
    }
    {
        timeit t(std::cout, "pvector time");
        pvector<int> q;
        for (unsigned i = 0; i < SZ1 + 1; i++) { q.push_back(i); }
        for (unsigned i = 0; i < N; i++) perf_pvector2(q, M);
    }
}
#endif

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
#ifdef PVECTOR_PERF_TEST
    tst_perf1();
    tst_perf2();
#endif
    return has_violations() ? 1 : 0;
}
