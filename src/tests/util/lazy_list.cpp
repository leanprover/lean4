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

template<typename T>
lazy_list<T> first(unsigned sz, lazy_list<T> l) {
    if (sz == 0 || !l) {
        return lazy_list<T>();
    } else {
        return lazy_list<T>(head(l), [=]() { return first(sz - 1, tail(l)); });
    }
}

template<typename T1, typename T2>
lazy_list<std::pair<T1, T2>> zip(lazy_list<T1> const & l1, lazy_list<T2> const & l2) {
    if (l1 && l2) {
        return lazy_list<std::pair<T1, T2>>(mk_pair(head(l1), head(l2)), [=]() { return zip(tail(l1), tail(l2)); });
    } else {
        return lazy_list<std::pair<T1, T2>>();
    }
}

template<typename T>
lazy_list<T> to_lazy(list<T> const & l) {
    if (l)
        return lazy_list<T>(head(l), [=]() { return to_lazy(tail(l)); });
    else
        return lazy_list<T>();
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
    for (auto c : first(30, zip(seq(1), fact_list()))) {
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
    return 0;
}
