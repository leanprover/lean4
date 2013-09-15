/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <deque>
#include <vector>
#include <ctime>
#include <random>
#include "util/test.h"
#include "util/pdeque.h"
using namespace lean;

// #define PDEQUE_PERF_TEST

/**
   \brief Naive equality test for debugging
*/
template<typename T>
bool operator==(pdeque<T> const & q1, pdeque<T> const & q2) {
    if (q1.size() != q2.size())
        return false;
    for (unsigned i = 0; i < q1.size(); i++) {
        if (q1[i] != q2[i])
            return false;
    }
    return true;
}


template<typename T>
bool operator==(pdeque<T> const & q1, std::deque<T> const & q2) {
    if (q1.size() != q2.size())
        return false;
    for (unsigned i = 0; i < q1.size(); i++) {
        if (q1[i] != q2[i])
            return false;
    }
    return true;
}

static void tst1() {
    pdeque<int> q;
    lean_assert(empty(q));
    lean_assert(size(q) == 0);
    q = push_back(q, 1);
    lean_assert(size(q) == 1);
    std::cout << "q: " << q << "\n";
    lean_assert(front(q) == 1);
    lean_assert(back(q) == 1);
    lean_assert(!empty(q));
    q = push_back(q, 2);
    lean_assert(front(q) == 1);
    lean_assert(back(q) == 2);
    std::cout << "q: " << q << "\n";
    q = push_front(q, 3);
    std::cout << "q: " << q << "\n";
    lean_assert(size(q) == 3);
    lean_assert(front(q) == 3);
    lean_assert(back(q) == 2);
    lean_assert(size(pop_front(q)) == 2);
    lean_assert(front(pop_front(q)) == 1);
    lean_assert(front(pop_front(pop_front(q))) == 2);
    lean_assert(empty(pop_front(pop_front(pop_front(q)))));
    lean_assert(pop_front(push_front(q, 3)) == q);
    lean_assert(pop_back(push_back(q, 3)) == q);
}

static void driver(unsigned max_sz, unsigned max_val, unsigned num_ops, double updt_freq, double copy_freq) {
    std::deque<int> q1;
    pdeque<int>     q2;
    pdeque<int>     q3;
    std::mt19937    rng; // the Mersenne Twister Random Number Generator with a popular choice of parameters

    rng.seed(static_cast<unsigned int>(time(0)));
    std::uniform_int_distribution<unsigned int> uint_dist;

    std::vector<pdeque<int>> copies;
    for (unsigned i = 0; i < num_ops; i++) {
        double f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < copy_freq)
            copies.push_back(q3);
        // read random positions of q3
        if (!empty(q3)) {
            for (unsigned int j = 0; j < uint_dist(rng) % 5; j++) {
                unsigned idx = uint_dist(rng) % size(q3);
                lean_assert(q3[idx] == q1[idx]);
            }
        }
        f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < updt_freq) {
            if (q1.size() >= max_sz)
                continue;
            int v = uint_dist(rng) % max_val;
            switch (uint_dist(rng) % 3) {
            case 0:
                q1.push_front(v);
                q2 = push_front(q2, v);
                q3.push_front(v);
                break;
            case 1:
                q1.push_back(v);
                q2 = push_back(q2, v);
                q3.push_back(v);
                break;
            default:
                if (!empty(q2)) {
                    unsigned idx = uint_dist(rng) % size(q2);
                    q1[idx] = v;
                    q2[idx] = v;
                    q3[idx] = v;
                    lean_assert(q1[idx] == q2[idx]);
                    lean_assert(q1[idx] == q3[idx]);
                }
                break;
            }
        } else {
            if (q1.size() == 0)
                continue;
            if (uint_dist(rng) % 2 == 0) {
                lean_assert(front(q2) == q1.front());
                lean_assert(front(q3) == q1.front());
                q1.pop_front();
                q2 = pop_front(q2);
                q3.pop_front();
            } else {
                lean_assert(back(q2) == q1.back());
                lean_assert(back(q3) == q1.back());
                q1.pop_back();
                q2 = pop_back(q2);
                q3.pop_back();
            }
        }
        lean_assert(q2 == q1);
        lean_assert(q3 == q1);
    }
    std::cout << "Copies created: " << copies.size() << "\n";
}

static void tst2() {
    driver(4,  32, 10000, 0.5, 0.01);
    driver(4,  32, 10000, 0.5, 0.3);
    driver(2,  32, 10000, 0.8, 0.5);
    driver(2,  32, 10000, 0.3, 0.01);
    driver(4,  32, 10000, 0.3, 0.5);
    driver(16, 32, 10000, 0.5, 0.1);
    driver(16, 32, 10000, 0.5, 0.01);
    driver(16, 32, 10000, 0.5, 0.5);
    driver(16, 32, 10000, 0.7, 0.1);
    driver(16, 32, 10000, 0.7, 0.5);
    driver(16, 32, 10000, 0.7, 0.01);
    driver(16, 32, 10000, 0.1, 0.1);
    driver(16, 32, 10000, 0.8, 0.1);
    driver(16, 32, 10000, 0.8, 0.3);
    driver(16, 1000, 10000, 0.8, 0.01);
    driver(16, 1000, 10000, 0.8, 0.0);
    driver(16, 1000, 10000, 0.8, 0.5);
    driver(16, 1000, 10000, 0.8, 0.1);
    driver(128, 1000, 10000, 0.5, 0.01);
    driver(128, 1000, 10000, 0.5, 0.1);
    driver(128, 1000, 10000, 0.5, 0.5);
    driver(128, 1000, 10000, 0.2, 0.1);
}

#ifdef PDEQUE_PERF_TEST
#include "util/timeit.h"

static void perf_deque(unsigned n) {
    std::deque<int> q;
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_front();
    }
}

static void perf_pdeque(unsigned n) {
    pdeque<int> q;
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_front();
    }
}

static void tst4() {
    unsigned N = 100000;
    unsigned M = 100;
    {
        timeit t(std::cout, "deque time");
        for (unsigned i = 0; i < N; i++) perf_deque(M);
    }
    {
        timeit t(std::cout, "pdeque time");
        for (unsigned i = 0; i < N; i++) perf_pdeque(M);
    }
}


static void perf_deque2(std::deque<int> q, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_front();
    }
}

static void perf_pdeque2(pdeque<int> q, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_front();
    }
}

static void tst5() {
    unsigned N = 100000;
    unsigned SZ1 = 10000;
    unsigned M   = 5;
    {
        timeit t(std::cout, "deque time");
        std::deque<int> q;
        for (unsigned i = 0; i < SZ1; i++) { q.push_back(i); }
        for (unsigned i = 0; i < N; i++) perf_deque2(q, M);
    }
    {
        timeit t(std::cout, "pdeque time");
        pdeque<int> q;
        for (unsigned i = 0; i < SZ1 + 1; i++) { q.push_back(i); }
        for (unsigned i = 0; i < N; i++) perf_pdeque2(q, M);
    }
}
#endif

int main() {
    tst1();
    tst2();
#ifdef PDEQUE_PERF_TEST
    tst4();
    tst5();
#endif
    return has_violations() ? 1 : 0;
}
