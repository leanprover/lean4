/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <utility>
#include "util/interrupt.h"
#include "util/test.h"
#include "util/optional.h"
#include "util/numerics/mpz.h"
#include "util/pair.h"
#include "util/lazy_list.h"
#include "util/lazy_list_fn.h"
#include "util/list.h"
using namespace lean;

lazy_list<int> seq(int s) {
    return mk_lazy_list<int>([=]() { return some(mk_pair(s, seq(s + 1))); });
}

lazy_list<int> from(int begin, int step, int end) {
    if (begin > end)
        return lazy_list<int>();
    else
        return mk_lazy_list<int>([=]() { return some(mk_pair(begin, from(begin + step, step, end))); });
}

lazy_list<mpz> fact_list_core(mpz i, mpz n) {
    return mk_lazy_list<mpz>([=]() { return some(mk_pair(n, fact_list_core(i+1, n*(i+1)))); });
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

lazy_list<int> loop() {
    return mk_lazy_list<int>([=]() {
            while (true) {
                check_interrupted();
            }
            return some(mk_pair(0, lazy_list<int>()));
        });
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
    lazy_list<int> l = mk_lazy_list<int>([]() { return some(mk_pair(10, lazy_list<int>())); });
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
#if defined(LEAN_MULTI_THREAD)
    display(timeout(append(append(take(10, seq(1)), loop()), seq(100)), 5));
    display(take(10, par(seq(1), loop())));
#endif
}

void tst2() {
    lazy_list<int> l(10);
    lean_assert(l.pull()->first == 10);
    lean_assert(!l.pull()->second.pull());
    display(l);
    lazy_list<int> l2(20, l);
    int i = 0;
    for_each(l2, [&](int v) {
            lean_assert(i != 0 || v == 20);
            lean_assert(i != 1 || v == 10);
            i++;
        });
    lean_assert(i == 2);
}

static void check(lazy_list<int> const & l, list<int> expected) {
    display(l);
    for_each(l, [&](int v) {
            lean_assert(expected);
            lean_assert(v == head(expected));
            expected = tail(expected);
        });
    lean_assert(!expected);
}

static void tst3() {
    check(repeat(1, [](int v) { if (v > 5) return lazy_list<int>(); else return lazy_list<int>(v+1); }),
          list<int>(6));
    // The following repeat produces the following "execution trace".
    // We use >> << to mark the element being processed
    // { >>1<< }       1 produces {2, 4}
    // { >>2<<, 4 }    2 produces {3, 6}
    // { >>3<<, 6, 4 }  3 produces {4, 8}
    // { >>4<<, 8, 6, 4 }   4 produces {5, 10}
    // { >>5<<, 10, 8, 6, 4 }  5 produces {6, 12}
    // { 6, 12, 10, 8, 6, >>4<< }  skips 6, 12, 10, 8, 6 since they are bigger than 5, and 4 produces {5, 10}
    // { 6, 12, 10, 8, 6, >>5<<, 10 } 5 produces {6, 12}
    // { 6, 12, 10, 8, 6, 6, 12, 10 } skips 6, 12, 10 since they are bigger than 5
    check(repeat(1, [](int v) { if (v > 5) return lazy_list<int>(); else return from(v+1, v+1, 2*(v + 1)); }),
          list<int>({6, 12, 10, 8, 6, 6, 12, 10}));
}

static void tst4() {
    // We use v:k to denote value v was produced with the given k.
    // When k == 0, the element is not processed.
    // Here is the execution trace for the following repeat_at_most
    // { 1:4 }
    // { 1:3, 2:3 }
    // { 1:2, 2:2, 2:3 }
    // { 1:1, 2:1, 2:2, 2:3 }
    // { 1:0, 2:0, 2:1, 2:2, 2:3 }
    // { 1:0, 2:0, 2:0, 4:0, 2:2, 2:3 }
    // { 1:0, 2:0, 2:0, 4:0, 2:1, 4:1, 2:3 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:1, 2:3 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:3 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:2, 4:2 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:1, 4:1, 4:2 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:0, 4:0, 4:1, 4:2 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:0, 4:0, 4:0, 8:0, 4:2 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:0, 4:0, 4:0, 8:0, 4:1, 8:1 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:0, 4:0, 4:0, 8:0, 4:0, 8:0, 8:1 }
    // { 1:0, 2:0, 2:0, 4:0, 2:0, 4:0, 4:0, 8:0, 2:0, 4:0, 4:0, 8:0, 4:0, 8:0, 8:0, 16:0 }
    // Thus, the final lazy list is
    // { 1, 2, 2, 4, 2, 4, 4, 8, 2, 4, 4, 8, 4, 8, 8, 16 }
    check(repeat_at_most(1, [](int v) { return from(v, v, 2*v); }, 4),
          list<int>({ 1, 2, 2, 4, 2, 4, 4, 8, 2, 4, 4, 8, 4, 8, 8, 16 }));
}

class gen {
    unsigned m_next;
public:
    gen():m_next(0) {}
    unsigned next() { unsigned r = m_next; m_next++; return r; }
};

lazy_list<unsigned> mk_gen(std::shared_ptr<gen> const & g) {
    return mk_lazy_list<unsigned>([=]() { return some(mk_pair(g->next(), mk_gen(g))); });
}

lazy_list<unsigned> mk_gen() {
    return mk_gen(std::make_shared<gen>());
}

void tst5() {
    auto l = mk_gen();
    display(take(10, l));
    display(take(10, l));
}

void tst6() {
    auto l = mk_gen();
    unsigned counter = 0;
    for_each(filter(take(10, l), [](unsigned v) { return v % 2 == 0; }), [&](unsigned) { counter++; });
    lean_assert(counter == 5);
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}
