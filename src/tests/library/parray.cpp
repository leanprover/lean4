/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <random>
#include <vector>
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/parray.h"
using namespace lean;

void tst1() {
    parray<unsigned> a(10, 0);
    lean_assert(a[0] == 0);
    lean_assert(a.size() == 10);
    parray<unsigned> b = a;
    a.set(0, 1);
    lean_assert(a[0] == 1);
    lean_assert(a[1] == 0);
    lean_assert(b[0] == 0);
    lean_assert(a[0] == 1);
}

void driver(unsigned max_sz, unsigned max_val, unsigned num_it,
            double push_back_freq,
            double pop_back_freq,
            double set_freq,
            double copy_freq) {
    parray<unsigned> v1;
    std::vector<unsigned> v2;
    std::mt19937   rng;
    rng.seed(static_cast<unsigned int>(time(0)));
    std::uniform_int_distribution<unsigned int> uint_dist;
    std::vector<std::pair<parray<unsigned>, std::vector<unsigned>>> copies;
    size_t acc_sz = 0;
    for (unsigned i = 0; i < num_it; i++) {
        acc_sz += v1.size();
        double f = static_cast<double>(uint_dist(rng) % 10000) / 10000.0;
        if (f < copy_freq) {
            copies.emplace_back(v1, v2);
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
        lean_assert(v1.size() == v2.size());
        for (unsigned i = 0; i < v2.size(); i++) {
            lean_assert(v1[i] == v2[i]);
        }
    }
    for (std::pair<parray<unsigned>, std::vector<unsigned>> const & p : copies) {
        lean_assert(p.first.size() == p.second.size());
        for (unsigned i = 0; i < p.second.size(); i++) {
            lean_assert(p.first[i] == p.second[i]);
        }
    }
    std::cout << "\n";
    std::cout << "Copies created:  " << copies.size() << "\n";
    std::cout << "Average size:    " << static_cast<double>(acc_sz) / static_cast<double>(num_it) << "\n";
}

static void tst2() {
    driver(4,  32, 10000, 0.5, 0.1, 0.5, 0.1);
    driver(4,  32, 10000, 0.5, 0.1, 0.5, 0.1);
    driver(4,  32, 10000, 0.5, 0.1, 0.5, 0.5);
    driver(16, 16, 100000, 0.5, 0.5, 0.5, 0.01);
    driver(16, 16, 100000, 0.5, 0.1, 0.5, 0.01);
    driver(16, 16, 100000, 0.5, 0.6, 0.5, 0.01);
    driver(16, 16, 10000, 0.5, 0.1, 0.5, 0.0);
}

static void tst3(unsigned n) {
    parray<unsigned> v1;
    v1.push_back(0);
    parray<unsigned> v2 = v1;
    for (unsigned i = 0; i < n; i++)
        v1.push_back(i);
    unsigned r = 0;
    for (unsigned i = 0; i < n; i++)
        r += v1[n - i - 1];
    std::cout << ">> " << r << "\n";
}

static void tst_perf(unsigned sz, unsigned n) {
    parray<unsigned> v1(sz, 0);
    parray<unsigned> v2 = v1;
    for (unsigned i = 0; i < sz; i++) {
        v1.set(i, i);
    }
    /* The following loop is very expensive without ensure_unshared */
    v1.ensure_unshared();
    for (unsigned i = 0; i < n; i++) {
        unsigned u1 = v1[i];
        unsigned u2 = v2[i];
        lean_assert(u1 == i);
        lean_assert(u2 == 0);
    }
}

class Foo {
    unsigned * m_data;
public:
    Foo():m_data(new unsigned(1)) {}
    Foo(Foo const & src):m_data(new unsigned(*src.m_data)) {}
    Foo(Foo && src):m_data(new unsigned(*src.m_data)) {}
    Foo(unsigned n):m_data(new unsigned(n)) {}
    ~Foo() { delete m_data; }

    Foo & operator=(Foo const & src) {
        *m_data = *src.m_data;
        return *this;
    }

    Foo & operator=(Foo const && src) {
        *m_data = *src.m_data;
        return *this;
    }

    unsigned get_val() const { return *m_data; }
};

static void tst4() {
    parray<Foo> v1;
    v1.push_back(Foo(2));
    v1.push_back(Foo(3));
    parray<Foo> v2 = v1;
    for (unsigned i = 0; i < 10; i++)
        v1.push_back(Foo(i));
    v1.set(0, Foo(100));
    v1.set(1, Foo(100));
    lean_assert(v2.size() == 2);
    lean_assert(v2[0].get_val() == 2);
    lean_assert(v2[1].get_val() == 3);
    parray<Foo> v3 = v1;
    v1.pop_back();
    v1.pop_back();
    lean_assert(v1.size() == 10);
    lean_assert(v3.size() == 12);
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_core_module();
    initialize_library_module();

    std::cout << "sizeof(parray::cell) = " << parray<unsigned>::sizeof_cell() << "\n";

    tst1();
    tst2();
    tst3(100000);
    tst4();
    tst_perf(100000, 10000);

    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
