/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <utility>
#include "util/test.h"
#include "util/optional.h"
#include "util/numerics/mpz.h"
#include "util/pair.h"
#include "util/lazy_list.h"
#include "util/lazy_list_fn.h"
#include "util/list.h"
using namespace lean;

lazy_list<int> seq(int s) {
    return lazy_list<int>([=]() { return some(mk_pair(s, seq(s + 1))); });
}

lazy_list<int> from(int begin, int step, int end) {
    if (begin > end)
        return lazy_list<int>();
    else
        return lazy_list<int>([=]() { return some(mk_pair(begin, from(begin + step, step, end))); });
}

lazy_list<mpz> fact_list_core(mpz i, mpz n) {
    return lazy_list<mpz>([=]() { return some(mk_pair(n, fact_list_core(i+1, n*(i+1)))); });
}

lazy_list<mpz> fact_list() {
    return fact_list_core(mpz(1), mpz(1));
}

lazy_list<int> mk_simple1(int y) {
    int x = 3;
    return map(map(append(from(10, 1, 15), from(20, 2, 25)), [=](int v) { return x + v; }),
               [=](int v) { return v - y; });
}

lazy_list<int> mk_simple2() {
    int x = 10;
    return filter(map(interleave(from(0, 2, 10), from(10, 3, 20)), [=](int v) { return x * v; }),
                  [](int v) { return v > 40; });
}

lazy_list<int> mk_simple3() {
    return map_append(from(0, 2, 100), [=](int v) { return from(1, 1, v); });
}

template<typename T>
void display(lazy_list<T> const & l) {
    int buffer[20000];
    int i = 0;
    for_each(l, [&](T const & v) {
            std::cout << v << " ";
            buffer[i] = i;
            i++;
        });
    std::cout << "\n";
}

static void tst1() {
    lazy_list<int> l([]() { return some(mk_pair(10, lazy_list<int>())); });
    lazy_list<int> empty;
    lean_assert(l.pull()->first == 10);
    lean_assert(!empty.pull());
    lean_assert(!l.pull()->second.pull());
    list<int> l2{1, 2, 3};
    int i = 1;
    for_each(to_lazy(l2), [&](int c) {
            std::cout << "c: " << c << ", i: " << i << "\n";
            lean_assert(c == i);
            i++;
        });
    display(mk_simple1(4));
    display(mk_simple2());
    display(take(10, fact_list()));
    display(take(20, mk_simple3()));
    display(orelse(take(10, seq(1)), take(10, seq(100))));
    display(orelse(take(10, seq(1)), lazy_list<int>()));
    display(orelse(lazy_list<int>(), take(10, seq(100))));
    display(orelse(take(0, seq(1)), take(10, seq(100))));
    display(orelse(filter(take(100, seq(1)), [](int i) { return i < 0; }), take(10, seq(1000))));
}

int main() {
    tst1();
    return 0;
}
