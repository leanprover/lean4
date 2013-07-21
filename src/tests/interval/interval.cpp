/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "interval.h"
#include "test.h"
#include "trace.h"
#include "mpq.h"
using namespace lean;

typedef interval<mpq> qi;
typedef std::vector<qi> qiv;

qiv mk_some_intervals(int low, int hi) {
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
    lean_assert(neg(t) == qi(-3, -1));
    lean_assert(neg(neg(t)) == t);
    lean_assert(qi(1, 2) + qi(2, 3) == qi(3, 5));
    lean_assert(qi(1, 5) + qi(-2, -3) == qi(-1, 2));
    for (auto i1 : mk_some_intervals(-2, 2))
        for (auto i2 : mk_some_intervals(-2, 2)) {
            auto r = i1 + i2;
            auto s = i1;
            s += i2;
            lean_assert(r == s);
            lean_assert(r.lower() == i1.lower() + i2.lower());
            lean_assert(r.upper() == i1.upper() + i2.upper());
            lean_assert(r.is_lower_open() == i1.is_lower_open() || i2.is_lower_open());
            lean_assert(r.is_upper_open() == i1.is_upper_open() || i2.is_upper_open());
            r -= i2;
            lean_assert(r.contains(i1));
            r = i1 - i2;
            s = i1;
            s -= i2;
            lean_assert(r == s);
            lean_assert(r.lower() == i1.lower() - i2.upper());
            lean_assert(r.upper() == i1.upper() - i2.lower());
            lean_assert(r.is_lower_open() == i1.is_lower_open() || i2.is_upper_open());
            lean_assert(r.is_upper_open() == i1.is_upper_open() || i2.is_lower_open());
            r -= r;
            lean_assert(r.contains_zero());
            r = i1 * i2;
            s = i1;
            s *= i2;
            lean_assert(r == s);
            lean_assert(r.lower() == std::min(i1.lower()*i2.lower(), std::min(i1.lower()*i2.upper(), std::min(i1.upper()*i2.lower(), i1.upper()*i2.upper()))));
            lean_assert(r.upper() == std::max(i1.lower()*i2.lower(), std::max(i1.lower()*i2.upper(), std::max(i1.upper()*i2.lower(), i1.upper()*i2.upper()))));
        }
    lean_assert(qi(1, 3).before(qi(4, 6)));
    lean_assert(!qi(1, 3).before(qi(3, 6)));
    lean_assert(qi(1, 3, true, true).before(qi(3, 6)));
}

static void tst2() {
    lean_assert(power(qi(2, 3), 2) == qi(4, 9));
    lean_assert(power(qi(-2, 3), 2) == qi(0, 9));
    lean_assert(power(qi(true, -2, 3, true), 2) == qi(false, 0, 9, true));
    lean_assert(power(qi(true, -4, 3, true), 2) == qi(false, 0, 16, true));
    lean_assert(power(qi(-3, -2), 2) == qi(4, 9));
    std::cout << power(qi(false, -3, -2, true), 2) << " --> " << qi(true, 4, 9, false) << "\n";
    lean_assert(power(qi(false, -3, -2, true), 2) == qi(true, 4, 9, false));
    lean_assert(power(qi(-3,-1), 3) == qi(-27, -1));
    lean_assert(power(qi(-3, 4), 3) == qi(-27, 64));
    lean_assert(power(qi(),3) == qi());
    lean_assert(power(qi(),2) == qi(false, 0)); // (-oo, oo)^2 == [0, oo)
}

int main() {
    continue_on_violation(true);
    enable_trace("numerics");
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}
