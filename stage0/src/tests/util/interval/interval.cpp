/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <algorithm>
#include "util/test.h"
#include "util/numerics/double.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpfp.h"
#include "util/interval/interval.h"

using namespace lean;

typedef interval<mpq> qi;
typedef interval<double> di;
typedef interval<mpfp> fi;
typedef std::vector<qi> qiv;

static qiv mk_some_intervals(int low, int hi) {
    qiv r;
    for (unsigned lo = 0; lo < 2; lo++)
    for (unsigned uo = 0; uo < 2; uo++)
    for (int l = low; l <= hi; l++)
    for (int u = l; u <= hi; u++) {
        if ((lo || uo) && l == u)
            continue;
        r.push_back(qi(lo, l, u, uo));
    }
    return r;
}

template<typename T> bool closed_endpoints(interval<T> const & i) { return !i.is_lower_open() && !i.is_upper_open(); }

static void tst1() {
    qi t(1, 3);
    std::cout << t + qi(2, 4, false, true) << "\n";
    std::cout << t << " --> " << inv(t) << "\n";
    lean_assert_eq(neg(t), qi(-3, -1));
    lean_assert_eq(neg(neg(t)), t);
    lean_assert_eq(qi(1, 2) + qi(2, 3), qi(3, 5));
    lean_assert_eq(qi(1, 5) + qi(-2, -3), qi(-1, 2));
    for (auto i1 : mk_some_intervals(-2, 2))
        for (auto i2 : mk_some_intervals(-2, 2)) {
            auto r = i1 + i2;
            auto s = i1;
            s += i2;
            lean_assert_eq(r, s);
            lean_assert_eq(r.lower(), i1.lower() + i2.lower());
            lean_assert_eq(r.upper(), i1.upper() + i2.upper());
            lean_assert(r.is_lower_open() == i1.is_lower_open() || i2.is_lower_open());
            lean_assert(r.is_upper_open() == i1.is_upper_open() || i2.is_upper_open());
            r -= i2;
            lean_assert(r.contains(i1));
            r = i1 - i2;
            s = i1;
            s -= i2;
            lean_assert_eq(r, s);
            lean_assert_eq(r.lower(), i1.lower() - i2.upper());
            lean_assert_eq(r.upper(), i1.upper() - i2.lower());
            lean_assert(r.is_lower_open() == i1.is_lower_open() || i2.is_upper_open());
            lean_assert(r.is_upper_open() == i1.is_upper_open() || i2.is_lower_open());
            r -= r;
            lean_assert(r.contains_zero());
            r = i1 * i2;
            s = i1;
            s *= i2;
            lean_assert_eq(r, s);
            lean_assert_eq(r.lower(), std::min(i1.lower()*i2.lower(), std::min(i1.lower()*i2.upper(), std::min(i1.upper()*i2.lower(), i1.upper()*i2.upper()))));
            lean_assert_eq(r.upper(), std::max(i1.lower()*i2.lower(), std::max(i1.lower()*i2.upper(), std::max(i1.upper()*i2.lower(), i1.upper()*i2.upper()))));
        }
    lean_assert(qi(1, 3).before(qi(4, 6)));
    lean_assert(!qi(1, 3).before(qi(3, 6)));
    lean_assert(qi(1, 3, true, true).before(qi(3, 6)));
}

static void tst2() {
    lean_assert_eq(power(qi(2, 3), 2), qi(4, 9));
    lean_assert_eq(power(qi(-2, 3), 2), qi(0, 9));
    lean_assert_eq(power(qi(true, -2, 3, true), 2), qi(false, 0, 9, true));
    lean_assert_eq(power(qi(true, -4, 3, true), 2), qi(false, 0, 16, true));
    lean_assert_eq(power(qi(-3, -2), 2), qi(4, 9));
    std::cout << power(qi(false, -3, -2, true), 2) << " --> " << qi(true, 4, 9, false) << "\n";
    lean_assert_eq(power(qi(false, -3, -2, true), 2), qi(true, 4, 9, false));
    lean_assert_eq(power(qi(-3, -1), 3), qi(-27, -1));
    lean_assert_eq(power(qi(-3, 4), 3), qi(-27, 64));
    lean_assert_eq(power(qi(), 3), qi());
    lean_assert_eq(power(qi(), 2), qi(false, 0)); // (-oo, oo)^2 == [0, oo)
}

static void check_deps(bound_deps const & deps, bool l1 = false, bool u1 = false, bool l2 = false, bool u2 = false) {
    lean_assert(l1 == dep_in_lower1(deps));
    lean_assert(u1 == dep_in_upper1(deps));
    lean_assert(l2 == dep_in_lower2(deps));
    lean_assert(u2 == dep_in_upper2(deps));
}

static void check_lower_deps(interval_deps const & deps, bool l1 = false, bool u1 = false, bool l2 = false, bool u2 = false) {
    check_deps(deps.m_lower_deps, l1, u1, l2, u2);
}

static void check_upper_deps(interval_deps const & deps, bool l1 = false, bool u1 = false, bool l2 = false, bool u2 = false) {
    check_deps(deps.m_upper_deps, l1, u1, l2, u2);
}

static void tst3() {
    qi i1(3, 10, false, true);
    qi i2(-8, 2, true, false);
    swap(i1, i2);
    lean_assert_eq(i1, qi(-8, 2, true, false));
    lean_assert_eq(i2, qi(3, 10, false, true));
    lean_assert(!qi(2, 3, true, true).contains(qi()));
    lean_assert(!qi(2, 10, true, true).contains(qi(0, 10, true, true)));
    lean_assert(!qi(2, 10, true, true).contains(qi(2, 10, false, true)));
    lean_assert(!qi(2, 10, true, true).contains(qi(true, 5)));
    lean_assert(!qi(2, 10, true, true).contains(qi(5, 11, true, true)));
    lean_assert(!qi(2, 10, true, true).contains(qi(5, 10, true, false)));
    lean_assert(!i1.is_empty());
    i1.set_empty();
    lean_assert(i1.is_empty());
    lean_assert(!i1.is_singleton());
    lean_assert(!i2.is_singleton());
    i1 = qi(4);
    lean_assert(i1.is_singleton());
    lean_assert(!qi(true, 1).before(qi(1, 2)));
    std::cout << qi(3, true) << "\n";
    lean_assert(!qi(1, 2).before(qi(3, true)));
    lean_assert(qi(1, 2).before(qi(3, 4)));
    interval_deps deps;
    qi().neg_jst(deps);
    lean_assert_eq(neg(qi()), qi());
    check_lower_deps(deps);
    check_upper_deps(deps);
    std::cout << qi(1, true) << "\n";
    qi(1, true).neg_jst(deps);
    lean_assert_eq(neg(qi(1, true)), qi(true, -1));
    check_lower_deps(deps, false, true);
    check_upper_deps(deps);
    qi(true, 1).neg_jst(deps);
    lean_assert_eq(neg(qi(true, 1)), qi(-1, true));
    check_lower_deps(deps);
    check_upper_deps(deps, true, false);
    qi(1, 3).neg_jst(deps);
    check_lower_deps(deps, false, true);
    check_upper_deps(deps, true, false);
    qi(1, 3).add_jst(qi(2, 4), deps);
    check_lower_deps(deps, true, false, true, false);
    check_upper_deps(deps, false, true, false, true);
    qi(1, 3).sub_jst(qi(2, 4), deps);
    check_lower_deps(deps, true, false, false, true);
    check_upper_deps(deps, false, true, true, false);
    qi i3(0);
    i3 *= mpq(3);
    lean_assert_eq(i3, qi(0));
    i3 /= mpq(4);
    lean_assert_eq(i3, qi(0));
}

int main() {
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
