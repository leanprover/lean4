/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <vector>
#include <random>
#include <ctime>
#include <unordered_set>
#include <sstream>
#include "util/test.h"
#include "util/buffer.h"
#include "util/rb_tree.h"
#include "util/timeit.h"
using namespace lean;

struct int_lt { int operator()(int i1, int i2) const { return i1 < i2 ? -1 : (i1 > i2 ? 1 : 0); } };
typedef rb_tree<int, int_lt> int_rb_tree;
typedef std::unordered_set<int> int_set;

void print(int_rb_tree const & t) {
    std::cout << t << "\n";
}

static void tst1() {
    int_rb_tree s;
    for (unsigned i = 0; i < 100; i++) {
        s.insert(i);
    }
    std::cout << s << "\n";
    std::cout << "DEPTH: " << s.get_depth() << "\n";
    int_rb_tree s2 = s;
    std::cout << "DEPTH: " << s2.get_depth() << "\n";
    s2.insert(200);
    lean_assert_eq(s2.size(), s.size() + 1);
    for (unsigned i = 0; i < 100; i++) {
        lean_assert(s.contains(i));
        lean_assert(s2.contains(i));
    }
    lean_assert(!s.contains(200));
    lean_assert(s2.contains(200));
}

static void tst2() {
    int_rb_tree s;
    s.insert(10);
    s.insert(11);
    s.insert(9);
    std::cout << s << "\n";
    int_rb_tree s2 = s;
    std::cout << s2 << "\n";
    s.insert(20);
    std::cout << s << "\n";
    s.insert(15);
}

static void tst3() {
    int_rb_tree s;
    s.insert(10);
    s.insert(3);
    s.insert(20);
    std::cout << s << "\n";
    s.insert(40);
    std::cout << s << "\n";
    s.insert(5);
    std::cout << s << "\n";
    s.insert(11);
    std::cout << s << "\n";
    s.insert(20);
    std::cout << s << "\n";
    s.insert(30);
    std::cout << s << "\n";
    s.insert(25);
    std::cout << s << "\n";
    s.insert(15);
    lean_assert(s.contains(40));
    lean_assert(s.contains(11));
    lean_assert(s.contains(20));
    lean_assert(s.contains(25));
    lean_assert(s.contains(5));
    lean_assert(s.contains(10));
    lean_assert(s.contains(3));
    lean_assert(s.contains(20));
    std::cout << s << "\n";
    int_rb_tree s2(s);
    std::cout << s2 << "\n";
    s.insert(34);
    std::cout << s2 << "\n";
    std::cout << s << "\n";
    int const * v = s.find(11);
    lean_assert(*v == 11);
    std::cout << s << "\n";
    lean_assert(!s.empty());
    s.clear();
    lean_assert(s.empty());
}

static bool operator==(int_set const & v1, int_rb_tree const & v2) {
    buffer<int> b;
    // std::cout << v2 << "\n";
    // std::for_each(v1.begin(), v1.end(), [](int v) { std::cout << v << " "; }); std::cout << "\n";
    v2.to_buffer(b);
    if (v1.size() != b.size())
        return false;
    for (unsigned i = 0; i < b.size(); i++) {
        if (v1.find(b[i]) == v1.end())
            return false;
    }
    return true;
}

static void driver(unsigned max_sz, unsigned max_val, unsigned num_ops, double insert_freq, double copy_freq) {
    int_set v1;
    int_rb_tree v2;
    int_rb_tree v3;
    std::mt19937   rng;
    size_t acc_sz = 0;
    size_t acc_depth = 0;
    rng.seed(static_cast<unsigned int>(time(0)));
    std::uniform_int_distribution<unsigned int> uint_dist;

    std::vector<int_rb_tree> copies;
    for (unsigned i = 0; i < num_ops; i++) {
        acc_sz += v1.size();
        acc_depth += v2.get_depth();
        double f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < copy_freq) {
            copies.push_back(v2);
        }
        f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        // read random positions of v3
        for (unsigned int j = 0; j < uint_dist(rng) % 5; j++) {
            int a = uint_dist(rng) % max_val;
            lean_assert(v3.contains(a) == (v1.find(a) != v1.end()));
        }
        if (f < insert_freq) {
            if (v1.size() >= max_sz)
                continue;
            int a = uint_dist(rng) % max_val;
            v1.insert(a);
            v2.insert(a);
            v3 = insert(v3, a);
        } else {
            int a = uint_dist(rng) % max_val;
            v1.erase(a);
            v2.erase(a);
            v3 = erase(v3, a);
        }
        lean_assert(v1 == v2);
        lean_assert(v1 == v3);
        lean_assert(v1.size() == v2.size());
    }
    std::cout << "\n";
    std::cout << "Copies created:  " << copies.size() << "\n";
    std::cout << "Average size:    " << static_cast<double>(acc_sz) / static_cast<double>(num_ops) << "\n";
    std::cout << "Average depth:   " << static_cast<double>(acc_depth) / static_cast<double>(num_ops) << "\n";
}

static void tst4() {
    driver(4,  32, 10000, 0.5, 0.01);
    driver(4,  10000, 10000, 0.5, 0.01);
    driver(16, 16, 10000, 0.5, 0.1);
    driver(128, 64, 10000, 0.5, 0.1);
    driver(128, 64, 10000, 0.4, 0.1);
    driver(128, 1000, 10000, 0.5, 0.5);
    driver(128, 1000, 10000, 0.5, 0.01);
    driver(1024, 10000, 10000, 0.8, 0.01);
}


static void tst5() {
    int_rb_tree s;
    s.insert(10);
    s.insert(20);
    lean_assert(s.find(30) == nullptr);
    lean_assert(*(s.find(20)) == 20);
    lean_assert(*(s.find(10)) == 10);
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}

