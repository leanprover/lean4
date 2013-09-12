/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#include <deque>
#include "test.h"
#include "queue.h"
using namespace lean;

/**
   \brief Naive equality test for debugging
*/
template<typename T>
bool operator==(queue<T> q1, queue<T> q2) {
    while (!is_empty(q1) && !is_empty(q2)) {
        auto p1 = pop_front(q1);
        auto p2 = pop_front(q2);
        if (p1.second != p2.second)
            return false;
        q1 = p1.first;
        q2 = p2.first;
    }
    return is_empty(q1) && is_empty(q2);
}


template<typename T>
bool operator==(queue<T> q1, std::deque<T> const & q2) {
    for (auto v : q2) {
        if (is_empty(q1))
            return false;
        auto p = pop_front(q1);
        if (p.second != v)
            return false;
        q1 = p.first;
    }
    return is_empty(q1);
}

static void tst1() {
    queue<int> q;
    lean_assert(is_empty(q));
    q = push_back(q, 1);
    lean_assert(pop_front(q).second == 1);
    lean_assert(pop_back(q).second  == 1);
    lean_assert(!is_empty(q));
    q = push_back(q, 2);
    q = push_front(q, 3);
    lean_assert(size(q) == 3);
    lean_assert(pop_front(q).second == 3);
    lean_assert(pop_back(q).second == 2);
    lean_assert(pop_front(q).first.size() == 2);
    std::cout << "q: " << q << "\n";
    std::cout << "pop_front(q): " << pop_front(q).first << "\n";
    lean_assert(pop_front(pop_front(q).first).second == 1);
    lean_assert(pop_front(pop_front(pop_front(q).first).first).second == 2);
    lean_assert(pop_front(pop_front(pop_front(q).first).first).first.is_empty());
    lean_assert(pop_front(push_front(q, 3)).first == q);
    lean_assert(pop_back(push_back(q, 3)).first == q);
}

static void driver(unsigned max_sz, unsigned max_val, unsigned num_ops, double push_freq) {
    std::deque<int> q1;
    queue<int>      q2;
    for (unsigned i = 0; i < num_ops; i++) {
        double f = static_cast<double>(std::rand() % 10000) / 10000.0;
        if (f < push_freq) {
            if (q1.size() >= max_sz)
                continue;
            int v = std::rand() % max_val;
            if (std::rand() % 2 == 0) {
                q1.push_front(v);
                lean_assert(pop_front(push_front(q2, v)).first == q2);
                q2 = push_front(q2, v);
            } else {
                q1.push_back(v);
                lean_assert(pop_back(push_back(q2, v)).first == q2);
                q2 = push_back(q2, v);
            }
        } else {
            if (q1.size() == 0)
                continue;
            if (std::rand() % 2 == 0) {
                auto p = pop_front(q2);
                lean_assert(p.second == q1.front());
                q1.pop_front();
                q2 = p.first;
            } else {
                auto p = pop_back(q2);
                lean_assert(p.second == q1.back());
                q1.pop_back();
                q2 = p.first;
            }
        }
        lean_assert(q2 == q1);
    }
}

static void tst2() {
    driver(4,  32, 10000, 0.5);
    driver(2,  32, 10000, 0.8);
    driver(2,  32, 10000, 0.3);
    driver(4,  32, 10000, 0.3);
    driver(16, 32, 10000, 0.5);
    driver(16, 32, 10000, 0.7);
    driver(16, 32, 10000, 0.1);
    driver(16, 32, 10000, 0.8);
    driver(16, 1000, 10000, 0.8);
    driver(128, 1000, 10000, 0.5);
    driver(128, 1000, 10000, 0.2);
}

static void tst3() {
    queue<int> q{1, 2, 3, 4};
    lean_assert(size(q) == 4);
    lean_assert(pop_back(q).second == 4);
    lean_assert(pop_front(q).second == 1);
    lean_assert(pop_front(pop_front(q).first).second == 2);
    lean_assert(pop_back(pop_back(q).first).second == 3);
}

// #define QUEUE_PERF_TEST
#ifdef QUEUE_PERF_TEST
#include "timeit.h"

static void perf_deque(unsigned n) {
    std::deque<int> q;
    for (unsigned i = 0; i < n; i++) {
        q.push_back(i);
    }
    for (unsigned i = 0; i < n; i++) {
        q.pop_front();
    }
}

static void perf_queue(unsigned n) {
    queue<int> q;
    for (unsigned i = 0; i < n; i++) {
        q = push_back(q, i);
    }
    for (unsigned i = 0; i < n; i++) {
        q = pop_front(q).first;
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
        timeit t(std::cout, "queue time");
        for (unsigned i = 0; i < N; i++) perf_queue(M);
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

static void perf_queue2(queue<int> q, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        q = push_back(q, i);
    }
    for (unsigned i = 0; i < n; i++) {
        q = pop_front(q).first;
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
        timeit t(std::cout, "queue time");
        queue<int> q;
        for (unsigned i = 0; i < SZ1 + 1; i++) { q = push_back(q, i); }
        q = pop_front(q).first;
        for (unsigned i = 0; i < N; i++) perf_queue2(q, M);
    }
}
#endif

int main() {
    tst1();
    tst2();
    tst3();
#ifdef QUEUE_PERF_TEST
    tst4();
    tst5();
#endif
    return has_violations() ? 1 : 0;
}
