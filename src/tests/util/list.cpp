/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "util/list.h"
#include "util/list_fn.h"
using namespace lean;

static void tst1() {
    list<int> l;
    lean_assert(is_nil(l));
    for (int i = 0; i < 10; i++) {
        list<int> old = l;
        l = list<int>(i, l);
        lean_assert(!is_nil(l));
        lean_assert(car(l) == i);
        lean_assert(is_eqp(cdr(l), old));
    }
    std::cout << l << "\n";
}

static void tst2() {
    std::vector<int> a{10, 20, 30};
    list<int> l = to_list(a.begin(), a.end());
    std::cout << l << "\n";
    lean_assert(head(l) == 10);
    lean_assert(head(tail(l)) == 20);
    lean_assert(head(tail(tail(l))) == 30);
    lean_assert(length(l) == 3);
}

static void tst3() {
    int a[3] = {10, 20, 30};
    list<int> l = to_list<int*>(a, a+3);
    std::cout << l << "\n";
    lean_assert(head(l) == 10);
    lean_assert(head(tail(l)) == 20);
    lean_assert(head(tail(tail(l))) == 30);
    lean_assert(length(l) == 3);
    lean_assert(length(list<int>()) == 0);
    lean_assert(length(list<int>(10, list<int>())) == 1);
    lean_assert(length(tail(list<int>(10, list<int>()))) == 0);
}

static void tst4() {
    list<int> l1{1, 2, 3};
    list<int> l2{1, 2, 3};
    lean_assert(l1 == l2);
    lean_assert(l1 != cons(1, l2));
    lean_assert(l1 != tail(l1));
    lean_assert(list<int>() == list<int>());
    lean_assert(l2 != list<int>());
    lean_assert(l1 != list<int>({1, 2, 3, 4}));
    lean_assert(l1 != tail(list<int>{1, 2, 3, 4}));
}

static void tst5() {
    for (unsigned n = 0; n < 16; n++) {
        buffer<int> tmp;
        for (unsigned i = 0; i < n; i++) { tmp.push_back(i); }
        buffer<int> tmp2;
        to_buffer(to_list(tmp.begin(), tmp.end()), tmp2);
        lean_assert(tmp2 == tmp);
        list<int> l = to_list(tmp.begin(), tmp.end());
        lean_assert(n == 0 || car(reverse(l)) == static_cast<int>(n - 1));
        lean_assert(reverse(reverse(l)) == l);
        auto p = split(l);
        list<int> l2 = append(p.first, p.second);
        lean_assert(l2 == l);
        lean_assert(-1 <= static_cast<int>(length(p.first)) - static_cast<int>(length(p.second)) && static_cast<int>(length(p.first)) - static_cast<int>(length(p.second)) <= 1);
    }
}

static void tst6() {
    lean_assert(list<int>(10) == list<int>{10});
}

static void tst7() {
    list<int> l{10, 20};
    list<int> l2(30, l);
    list<int> l3(30, l);
    lean_assert(l2 == l3);
}

static void tst8() {
    list<int> l1{1, 2, 3};
    unsigned c = 0;
    for_each(l1, [&](int ){ c = c + 1; });
    lean_assert(c == length(l1));
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    return has_violations() ? 1 : 0;
}
