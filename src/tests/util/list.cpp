/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <utility>
#include "util/test.h"
#include "util/list.h"
#include "util/list_fn.h"
#include "util/timeit.h"
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

static void tst9(int sz) {
    list<int> l;
    for (int i = 0; i < sz; i++) {
        l = cons(i, l);
    }
    l = map_reuse(l, [&](int v) { return v > 90 ? v + 10 : v; });
    std::cout << l << "\n";
    unsigned sum = 0;
    int j = length(l);
    for (auto i : l) {
        --j;
        lean_assert(j > 90 || i == j);
        sum += i;
    }
    auto l2 = map_reuse(l, [&](int v) { return v; });
    lean_assert(l == l2);
    auto l3 = map_reuse(l2, [&](int v) { return v + 2; });
    lean_assert(compare(l2, l3, [](int v1, int v2) { return v1 + 2 == v2; }));
    std::cout << l3 << "\n";
}

static void tst10(int sz, int num) {
    list<int> l;
    for (int i = 0; i < sz; i++) {
        l = cons(i, l);
    }
    {
        timeit timer(std::cout, "for_each");
        unsigned sum = 0;
        for (int i = 0; i < num; i++) {
            sum = 0;
            for_each(l, [&](int v) { sum += v; });
        }
        std::cout << "sum: " << sum << "\n";
    }
}

static void tst11(int sz, int num) {
    list<int> l;
    for (int i = 0; i < sz; i++) {
        l = cons(i, l);
    }
    list<int> l2;
    {
        timeit timer(std::cout, "map");
        for (int i = 0; i < num; i++) {
            l2 = map(l, [&](int v) { return v; });
        }
    }
    lean_assert(l == l2);
}

static void tst12() {
    list<pair<int, char const *>> l;
    lean_assert(is_nil(l));
    l.emplace_front(20, "world");
    l.emplace_front(10, "hello");
    int sum = 0;
    for (auto p : l) {
        sum += p.first;
        std::cout << p.second << " ";
    }
    std::cout << "\n";
    lean_assert(sum == 30);
}

static void tst13() {
    list<int> l({1, 2, 3, 4, 5, 6, 7});
    list<int> l2 = map_filter<int>(l, [](int in, int & out) {
            if (in % 2 == 0) {
                out = in + 10;
                return true;
            } else {
                return false;
            }
        });
    std::cout << l2 << "\n";
    list<int> l3({12, 14, 16});
    lean_assert_eq(l2, l3);
    lean_assert(empty(map_filter<int>(l, [](int, int &) { return false; })));
    lean_assert(empty(map_filter<int>(list<int>(), [](int in, int & out) { out = in; return true; })));
}

static void tst14() {
    list<int> l({1, 2, 3, 4, 5, 6, 7, 8});
    lean_assert_eq(filter(l, [](int i) { return i % 2 == 0; }), list<int>({2, 4, 6, 8}));
    lean_assert_eq(filter(l, [](int i) { return i < 3; }), list<int>({1, 2}));
    lean_assert_eq(filter(l, [](int i) { return i > 10; }), list<int>());
    lean_assert_eq(filter(l, [](int i) { return i > 5; }), list<int>({6, 7, 8}));
    lean_assert_eq(filter(l, [](int i) { return i % 3 == 0; }), list<int>({3, 6}));
}

static list<int> range(int l, int u) {
    if (l > u)
        return list<int>();
    else
        return cons(l, range(l+1, u));
}

static void tst15() {
    list<int> l({1, 2, 3, 4});
    std::cout << map_append(l, [](int i) { return range(1, i); }) << "\n";
    lean_assert_eq(map_append(l, [](int i) { return range(1, i); }), list<int>({1, 1, 2, 1, 2, 3, 1, 2, 3, 4}));
    lean_assert_eq(map_append(l, [](int i) { return i == 2 ? list<int>({2, 2, 2}) : list<int>(i); }),
                   list<int>({1, 2, 2, 2, 3, 4}));
}

static void tst16() {
    list<int> l({1, 2, 3, 4});
    lean_assert_eq(map(l, [](int i) { return i + 10; }),
                   list<int>({11, 12, 13, 14}));
    lean_assert_eq(map(list<int>(), [](int i) { return i + 10; }), list<int>());
}

static void tst17() {
    list<int> l({1, 2, 3, 4});
    lean_assert(is_eqp(filter(l, [](int v) { return v < 10; }), l));
    list<int> l2(filter(l, [](int v) { return v != 1; }));
    lean_assert(is_eqp(tail(l), l2));
    list<int> l3(filter(l, [](int v) { return v != 2; }));
    lean_assert(is_eqp(tail(tail(l)), tail(l2)));
}

static void tst18() {
    list<int> l({1, 2, 3, 4, 5});
    lean_assert_eq(remove_last(l, [](int v) { return v % 2 == 0; }), list<int>({1, 2, 3, 5}));
    lean_assert_eq(remove_last(l, [](int v) { return v < 0; }), l);
    lean_assert(is_eqp(remove_last(l, [](int v) { return v < 0; }), l));
    list<int> l2 = remove_last(l, [](int v) { return v < 3; });
    lean_assert_eq(l2, list<int>({1, 3, 4, 5}));
    lean_assert(is_eqp(tail(tail(l)), tail(l2)));
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
    tst9(100);
    tst10(1000, 5);
    tst11(1000, 5);
    tst12();
    tst13();
    tst14();
    tst15();
    tst16();
    tst17();
    tst18();
    return has_violations() ? 1 : 0;
}
