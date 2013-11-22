/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <utility>
#include "util/test.h"
#include "util/numerics/mpz.h"
#include "util/pair.h"
#include "util/lazy_list.h"
#include "util/lazy_list_fn.h"
#include "util/list.h"
using namespace lean;

lazy_list<int> seq(int s) {
    return lazy_list<int>(s, [=]() { return seq(s + 1); });
}

lazy_list<int> from(int begin, int step, int end) {
    if (begin > end)
        return lazy_list<int>();
    else
        return lazy_list<int>(begin, [=]() { return from(begin + step, step, end); });
}

lazy_list<mpz> fact_list_core(mpz i, mpz n) {
    return lazy_list<mpz>(n, [=]() { return fact_list_core(i+1, n*(i+1)); });
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
    for (auto v : l) {
        std::cout << v << " ";
    }
    std::cout << "\n";
}

int main() {
    lean_assert(head(lazy_list<int>(10)) == 10);
    lean_assert(!lazy_list<int>());
    lean_assert(!tail(lazy_list<int>(10)));
    lazy_list<int> l(-10, from(10, 20, 100));
    l = cons(-20, l);
    lean_assert(head(l) == -20);
    for (auto c : l) {
        std::cout << c << "\n";
    }
    int i = 1;
    for (auto c : take(30, zip(seq(1), fact_list()))) {
        lean_assert(c.first == i);
        std::cout << c.first << " " << c.second << "\n";
        i++;
    }
    list<int> l2{1, 2, 3};
    i = 1;
    for (auto c : to_lazy(l2)) {
        lean_assert(c == i);
        i++;
    }
    display(mk_simple1(4));
    display(mk_simple2());
    display(take(12, mk_simple3()));
    return 0;
}
