/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "test.h"
#include "trace.h"
#include "double.h"
#include "mpq.h"
#include "mpfp.h"
#include "interval_def.h"

using namespace lean;

typedef interval<double> qi;
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

static void double_interval_trans() {
    di i1(1.0, 2.0);
    std::cout << "power(" << i1 << ", 3) = " << power(i1, 3) << std::endl;
    std::cout << "exp(" << i1 << ") = "      << exp(i1) << std::endl;
    std::cout << "log(" << i1 << ") = "      << log(i1) << std::endl;
}

template<typename T1, typename T2, typename T3>
void print_result(T1 a, std::string const & op, T2 b, T3 r) {
    std::cout << a << " " << op << " " << b << " = " << r << std::endl;
}

template<typename T, typename F>
void print_result_fun(F f, std::string const & fun, T x) {
    std::cout << fun << "(" << x << ") = " << f(x) << std::endl;
}

static void mpfr_interval_inf1() {
    fi i1(1.0, 2.0);
    fi inf;
    fi ozero_pinf;
    fi ozero_ninf;
    ozero_pinf.set_is_lower_inf(false);
    ozero_ninf.set_is_upper_inf(false);
    fi czero_pinf;
    fi czero_ninf;
    czero_pinf.set_is_lower_inf(false);
    czero_pinf.set_is_lower_open(false);
    czero_ninf.set_is_upper_inf(false);
    czero_ninf.set_is_upper_open(false);

    std::cerr << i1 << " * " << ozero_ninf << " = " << i1 * ozero_ninf << std::endl;
    std::cerr << i1 << " * " << ozero_pinf << " = " << i1 * ozero_pinf << std::endl;
    std::cerr << i1 << " * " << czero_ninf << " = " << i1 * czero_ninf << std::endl;
    std::cerr << i1 << " * " << czero_pinf << " = " << i1 * czero_pinf << std::endl;
    lean_assert(i1 * ozero_ninf == ozero_ninf); lean_assert(ozero_ninf * i1 == ozero_ninf);
    lean_assert(i1 * ozero_pinf == ozero_pinf); lean_assert(ozero_pinf * i1 == ozero_pinf);
    lean_assert(i1 * czero_ninf == czero_ninf); lean_assert(czero_ninf * i1 == czero_ninf);
    lean_assert(i1 * czero_pinf == czero_pinf); lean_assert(czero_pinf * i1 == czero_pinf);

    std::cerr << "=== Addition between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << std::endl;
    std::cerr << ozero_ninf << " + " << ozero_ninf << " = " << ozero_ninf + ozero_ninf << std::endl;
    std::cerr << ozero_ninf << " + " << ozero_pinf << " = " << ozero_ninf + ozero_pinf << std::endl;
    std::cerr << ozero_ninf << " + " << czero_ninf << " = " << ozero_ninf + czero_ninf << std::endl;
    std::cerr << ozero_ninf << " + " << czero_pinf << " = " << ozero_ninf + czero_pinf << std::endl;
    std::cerr << ozero_pinf << " + " << ozero_ninf << " = " << ozero_pinf + ozero_ninf << std::endl;
    std::cerr << ozero_pinf << " + " << ozero_pinf << " = " << ozero_pinf + ozero_pinf << std::endl;
    std::cerr << ozero_pinf << " + " << czero_ninf << " = " << ozero_pinf + czero_ninf << std::endl;
    std::cerr << ozero_pinf << " + " << czero_pinf << " = " << ozero_pinf + czero_pinf << std::endl;
    std::cerr << czero_ninf << " + " << ozero_ninf << " = " << czero_ninf + ozero_ninf << std::endl;
    std::cerr << czero_ninf << " + " << ozero_pinf << " = " << czero_ninf + ozero_pinf << std::endl;
    std::cerr << czero_ninf << " + " << czero_ninf << " = " << czero_ninf + czero_ninf << std::endl;
    std::cerr << czero_ninf << " + " << czero_pinf << " = " << czero_ninf + czero_pinf << std::endl;
    std::cerr << czero_pinf << " + " << ozero_ninf << " = " << czero_pinf + ozero_ninf << std::endl;
    std::cerr << czero_pinf << " + " << ozero_pinf << " = " << czero_pinf + ozero_pinf << std::endl;
    std::cerr << czero_pinf << " + " << czero_ninf << " = " << czero_pinf + czero_ninf << std::endl;
    std::cerr << czero_pinf << " + " << czero_pinf << " = " << czero_pinf + czero_pinf << std::endl;

    lean_assert(ozero_ninf + ozero_ninf == ozero_ninf);
    lean_assert(ozero_ninf + ozero_pinf == inf);
    lean_assert(ozero_ninf + czero_ninf == ozero_ninf);
    lean_assert(ozero_ninf + czero_pinf == inf);
    lean_assert(ozero_pinf + ozero_ninf == inf);
    lean_assert(ozero_pinf + ozero_pinf == ozero_pinf);
    lean_assert(ozero_pinf + czero_ninf == inf);
    lean_assert(ozero_pinf + czero_pinf == ozero_pinf);
    lean_assert(czero_ninf + ozero_ninf == ozero_ninf);
    lean_assert(czero_ninf + ozero_pinf == inf);
    lean_assert(czero_ninf + czero_ninf == czero_ninf);
    lean_assert(czero_ninf + czero_pinf == inf);
    lean_assert(czero_pinf + ozero_ninf == inf);
    lean_assert(czero_pinf + ozero_pinf == ozero_pinf);
    lean_assert(czero_pinf + czero_ninf == inf);
    lean_assert(czero_pinf + czero_pinf == czero_pinf);

    std::cerr << "=== Subtraction between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << std::endl;
    std::cerr << ozero_ninf << " - " << ozero_ninf << " = " << ozero_ninf - ozero_ninf << std::endl;
    std::cerr << ozero_ninf << " - " << ozero_pinf << " = " << ozero_ninf - ozero_pinf << std::endl;
    std::cerr << ozero_ninf << " - " << czero_ninf << " = " << ozero_ninf - czero_ninf << std::endl;
    std::cerr << ozero_ninf << " - " << czero_pinf << " = " << ozero_ninf - czero_pinf << std::endl;
    std::cerr << ozero_pinf << " - " << ozero_ninf << " = " << ozero_pinf - ozero_ninf << std::endl;
    std::cerr << ozero_pinf << " - " << ozero_pinf << " = " << ozero_pinf - ozero_pinf << std::endl;
    std::cerr << ozero_pinf << " - " << czero_ninf << " = " << ozero_pinf - czero_ninf << std::endl;
    std::cerr << ozero_pinf << " - " << czero_pinf << " = " << ozero_pinf - czero_pinf << std::endl;
    std::cerr << czero_ninf << " - " << ozero_ninf << " = " << czero_ninf - ozero_ninf << std::endl;
    std::cerr << czero_ninf << " - " << ozero_pinf << " = " << czero_ninf - ozero_pinf << std::endl;
    std::cerr << czero_ninf << " - " << czero_ninf << " = " << czero_ninf - czero_ninf << std::endl;
    std::cerr << czero_ninf << " - " << czero_pinf << " = " << czero_ninf - czero_pinf << std::endl;
    std::cerr << czero_pinf << " - " << ozero_ninf << " = " << czero_pinf - ozero_ninf << std::endl;
    std::cerr << czero_pinf << " - " << ozero_pinf << " = " << czero_pinf - ozero_pinf << std::endl;
    std::cerr << czero_pinf << " - " << czero_ninf << " = " << czero_pinf - czero_ninf << std::endl;
    std::cerr << czero_pinf << " - " << czero_pinf << " = " << czero_pinf - czero_pinf << std::endl;

    lean_assert(ozero_ninf - ozero_ninf == inf);
    lean_assert(ozero_ninf - ozero_pinf == ozero_ninf);
    lean_assert(ozero_ninf - czero_ninf == inf);
    lean_assert(ozero_ninf - czero_pinf == ozero_ninf);
    lean_assert(ozero_pinf - ozero_ninf == ozero_pinf);
    lean_assert(ozero_pinf - ozero_pinf == inf);
    lean_assert(ozero_pinf - czero_ninf == ozero_pinf);
    lean_assert(ozero_pinf - czero_pinf == inf);
    lean_assert(czero_ninf - ozero_ninf == inf);
    lean_assert(czero_ninf - ozero_pinf == ozero_ninf);
    lean_assert(czero_ninf - czero_ninf == inf);
    lean_assert(czero_ninf - czero_pinf == czero_ninf);
    lean_assert(czero_pinf - ozero_ninf == ozero_pinf);
    lean_assert(czero_pinf - ozero_pinf == inf);
    lean_assert(czero_pinf - czero_ninf == czero_pinf);
    lean_assert(czero_pinf - czero_pinf == inf);

    std::cerr << "=== Multiplication between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << std::endl;
    std::cerr << ozero_ninf << " * " << ozero_ninf << " = " << ozero_ninf * ozero_ninf << std::endl;
    std::cerr << ozero_ninf << " * " << ozero_pinf << " = " << ozero_ninf * ozero_pinf << std::endl;
    std::cerr << ozero_ninf << " * " << czero_ninf << " = " << ozero_ninf * czero_ninf << std::endl;
    std::cerr << ozero_ninf << " * " << czero_pinf << " = " << ozero_ninf * czero_pinf << std::endl;
    std::cerr << ozero_pinf << " * " << ozero_ninf << " = " << ozero_pinf * ozero_ninf << std::endl;
    std::cerr << ozero_pinf << " * " << ozero_pinf << " = " << ozero_pinf * ozero_pinf << std::endl;
    std::cerr << ozero_pinf << " * " << czero_ninf << " = " << ozero_pinf * czero_ninf << std::endl;
    std::cerr << ozero_pinf << " * " << czero_pinf << " = " << ozero_pinf * czero_pinf << std::endl;
    std::cerr << czero_ninf << " * " << ozero_ninf << " = " << czero_ninf * ozero_ninf << std::endl;
    std::cerr << czero_ninf << " * " << ozero_pinf << " = " << czero_ninf * ozero_pinf << std::endl;
    std::cerr << czero_ninf << " * " << czero_ninf << " = " << czero_ninf * czero_ninf << std::endl;
    std::cerr << czero_ninf << " * " << czero_pinf << " = " << czero_ninf * czero_pinf << std::endl;
    std::cerr << czero_pinf << " * " << ozero_ninf << " = " << czero_pinf * ozero_ninf << std::endl;
    std::cerr << czero_pinf << " * " << ozero_pinf << " = " << czero_pinf * ozero_pinf << std::endl;
    std::cerr << czero_pinf << " * " << czero_ninf << " = " << czero_pinf * czero_ninf << std::endl;
    std::cerr << czero_pinf << " * " << czero_pinf << " = " << czero_pinf * czero_pinf << std::endl;

    lean_assert(ozero_ninf * ozero_ninf == ozero_pinf);
    lean_assert(ozero_ninf * ozero_pinf == ozero_ninf);
    lean_assert(ozero_ninf * czero_ninf == czero_pinf);
    lean_assert(ozero_ninf * czero_pinf == czero_ninf);
    lean_assert(ozero_pinf * ozero_ninf == ozero_ninf);
    lean_assert(ozero_pinf * ozero_pinf == ozero_pinf);
    lean_assert(ozero_pinf * czero_ninf == czero_ninf);
    lean_assert(ozero_pinf * czero_pinf == czero_pinf);
    lean_assert(czero_ninf * ozero_ninf == czero_pinf);
    lean_assert(czero_ninf * ozero_pinf == czero_ninf);
    lean_assert(czero_ninf * czero_ninf == czero_pinf);
    lean_assert(czero_ninf * czero_pinf == czero_ninf);
    lean_assert(czero_pinf * ozero_ninf == czero_ninf);
    lean_assert(czero_pinf * ozero_pinf == czero_pinf);
    lean_assert(czero_pinf * czero_ninf == czero_ninf);
    lean_assert(czero_pinf * czero_pinf == czero_pinf);

    std::cerr << "=== Division between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << std::endl;
    std::cerr << ozero_ninf << " / " << ozero_ninf << " = " << ozero_ninf / ozero_ninf << std::endl;
    std::cerr << ozero_ninf << " / " << ozero_pinf << " = " << ozero_ninf / ozero_pinf << std::endl;
    std::cerr << ozero_pinf << " / " << ozero_ninf << " = " << ozero_pinf / ozero_ninf << std::endl;
    std::cerr << ozero_pinf << " / " << ozero_pinf << " = " << ozero_pinf / ozero_pinf << std::endl;
    std::cerr << czero_ninf << " / " << ozero_ninf << " = " << czero_ninf / ozero_ninf << std::endl;
    std::cerr << czero_ninf << " / " << ozero_pinf << " = " << czero_ninf / ozero_pinf << std::endl;
    std::cerr << czero_pinf << " / " << ozero_ninf << " = " << czero_pinf / ozero_ninf << std::endl;
    std::cerr << czero_pinf << " / " << ozero_pinf << " = " << czero_pinf / ozero_pinf << std::endl;

    lean_assert(ozero_ninf / ozero_ninf == ozero_pinf);
    lean_assert(ozero_ninf / ozero_pinf == ozero_ninf);
    lean_assert(ozero_pinf / ozero_ninf == ozero_ninf);
    lean_assert(ozero_pinf / ozero_pinf == ozero_pinf);
    lean_assert(czero_ninf / ozero_ninf == czero_pinf);
    lean_assert(czero_ninf / ozero_pinf == czero_ninf);
    lean_assert(czero_pinf / ozero_ninf == czero_ninf);
    lean_assert(czero_pinf / ozero_pinf == czero_pinf);
}

static void mpfr_interval_inf2() {
    fi i1(1.0, 2.0);
    fi i2(3.0, 4.0);
    fi i3(-10.0, -5.0);
    fi i4(-3.0, +4.0);
    fi i5(5.0, 8.0);
    fi inf;

    mpfp c1(0.6);
    mpfp c2(3.0);
    mpfp c3(-0.3);
    mpfp c4(-4.5);
    mpfp zero(0.0);

    lean_assert(i1 + inf == inf);   lean_assert(inf + i1 == inf);
    lean_assert(i2 + inf == inf);   lean_assert(inf + i2 == inf);
    lean_assert(i3 + inf == inf);   lean_assert(inf + i3 == inf);
    lean_assert(i4 + inf == inf);   lean_assert(inf + i4 == inf);
    lean_assert(i5 + inf == inf);   lean_assert(inf + i5 == inf);
    lean_assert(c1 + inf == inf);   lean_assert(inf + c1 == inf);
    lean_assert(c2 + inf == inf);   lean_assert(inf + c2 == inf);
    lean_assert(c3 + inf == inf);   lean_assert(inf + c3 == inf);
    lean_assert(c4 + inf == inf);   lean_assert(inf + c4 == inf);
    lean_assert(zero + inf == inf); lean_assert(inf + zero == inf);

    lean_assert(i1 - inf == inf);   lean_assert(inf - i1 == inf);
    lean_assert(i2 - inf == inf);   lean_assert(inf - i2 == inf);
    lean_assert(i3 - inf == inf);   lean_assert(inf - i3 == inf);
    lean_assert(i4 - inf == inf);   lean_assert(inf - i4 == inf);
    lean_assert(i5 - inf == inf);   lean_assert(inf - i5 == inf);
    lean_assert(c1 - inf == inf);   lean_assert(inf - c1 == inf);
    lean_assert(c2 - inf == inf);   lean_assert(inf - c2 == inf);
    lean_assert(c3 - inf == inf);   lean_assert(inf - c3 == inf);
    lean_assert(c4 - inf == inf);   lean_assert(inf - c4 == inf);
    lean_assert(zero - inf == inf); lean_assert(inf - zero == inf);

    lean_assert(i1 * inf == inf);   lean_assert(inf * i1 == inf);
    lean_assert(i2 * inf == inf);   lean_assert(inf * i2 == inf);
    lean_assert(i3 * inf == inf);   lean_assert(inf * i3 == inf);
    lean_assert(i4 * inf == inf);   lean_assert(inf * i4 == inf);
    lean_assert(i5 * inf == inf);   lean_assert(inf * i5 == inf);
    lean_assert(c1 * inf == inf);   lean_assert(inf * c1 == inf);
    lean_assert(c2 * inf == inf);   lean_assert(inf * c2 == inf);
    lean_assert(c3 * inf == inf);   lean_assert(inf * c3 == inf);
    lean_assert(c4 * inf == inf);   lean_assert(inf * c4 == inf);
    lean_assert(zero * inf == zero);lean_assert(inf * zero == zero);

}

static void mpfr_interval_arith() {
    fi i1(1.0, 2.0);
    fi i2(3.0, 4.0);
    fi i3(-10.0, -5.0);
    fi i4(-3.0, +4.0);
    fi i5(5.0, 8.0);

    mpfp c1(0.6);
    mpfp c2(3.0);
    mpfp c3(0.0);
    mpfp c4(-4.5);
    mpfp c5(-0.3);

    std::cout << "=====================" << std::endl;
    print_result(i1, "+", c1, i1 + c1);
    print_result(i2, "+", c2, i2 + c2);
    print_result(i3, "+", c3, i3 + c3);
    print_result(i4, "+", c4, i4 + c4);
    print_result(i5, "+", c5, i5 + c5);
    print_result(i5, "+", c1, i5 + c1);
    print_result(i4, "+", c2, i4 + c2);
    print_result(i2, "+", c4, i2 + c4);
    print_result(i1, "+", c5, i1 + c5);

    std::cout << "=====================" << std::endl;
    print_result(c1, "+", i1, c1 + i1);
    print_result(c2, "+", i2, c2 + i2);
    print_result(c3, "+", i3, c3 + i3);
    print_result(c4, "+", i4, c4 + i4);
    print_result(c5, "+", i5, c5 + i5);
    print_result(c5, "+", i1, c5 + i1);
    print_result(c4, "+", i2, c4 + i2);
    print_result(c2, "+", i4, c2 + i4);
    print_result(c1, "+", i5, c1 + i5);

    std::cout << "=====================" << std::endl;
    print_result(i1, "-", c1, i1 - c1);
    print_result(i2, "-", c2, i2 - c2);
    print_result(i3, "-", c3, i3 - c3);
    print_result(i4, "-", c4, i4 - c4);
    print_result(i5, "-", c5, i5 - c5);
    print_result(i5, "-", c1, i5 - c1);
    print_result(i4, "-", c2, i4 - c2);
    print_result(i2, "-", c4, i2 - c4);
    print_result(i1, "-", c5, i1 - c5);

    std::cout << "=====================" << std::endl;
    print_result(c1, "-", i1, c1 - i1);
    print_result(c2, "-", i2, c2 - i2);
    print_result(c3, "-", i3, c3 - i3);
    print_result(c4, "-", i4, c4 - i4);
    print_result(c5, "-", i5, c5 - i5);
    print_result(c5, "-", i1, c5 - i1);
    print_result(c4, "-", i2, c4 - i2);
    print_result(c2, "-", i4, c2 - i4);
    print_result(c1, "-", i5, c1 - i5);

    std::cout << "=====================" << std::endl;
    print_result(i1, "*", c1, i1 * c1);
    print_result(i2, "*", c2, i2 * c2);
    print_result(i3, "*", c3, i3 * c3);
    print_result(i4, "*", c4, i4 * c4);
    print_result(i5, "*", c5, i5 * c5);
    print_result(i5, "*", c1, i5 * c1);
    print_result(i4, "*", c2, i4 * c2);
    print_result(i2, "*", c4, i2 * c4);
    print_result(i1, "*", c5, i1 * c5);

    std::cout << "=====================" << std::endl;
    print_result(c1, "*", i1, c1 * i1);
    print_result(c2, "*", i2, c2 * i2);
    print_result(c3, "*", i3, c3 * i3);
    print_result(c4, "*", i4, c4 * i4);
    print_result(c5, "*", i5, c5 * i5);
    print_result(c5, "*", i1, c5 * i1);
    print_result(c4, "*", i2, c4 * i2);
    print_result(c2, "*", i4, c2 * i4);
    print_result(c1, "*", i5, c1 * i5);

    std::cout << "=====================" << std::endl;
    print_result(i1, "/", c1, i1 / c1);
    print_result(i2, "/", c2, i2 / c2);
    print_result(i3, "/", c3, i3 / c3);
    print_result(i4, "/", c4, i4 / c4);
    print_result(i5, "/", c5, i5 / c5);
    print_result(i5, "/", c1, i5 / c1);
    print_result(i4, "/", c2, i4 / c2);
    print_result(i2, "/", c4, i2 / c4);
    print_result(i1, "/", c5, i1 / c5);

    std::cout << "=====================" << std::endl;
    print_result(c1, "/", i1, c1 / i1);
    print_result(c2, "/", i2, c2 / i2);
    print_result(c3, "/", i3, c3 / i3);
    print_result(c5, "/", i5, c5 / i5);
    print_result(c5, "/", i1, c5 / i1);
    print_result(c4, "/", i2, c4 / i2);
    print_result(c1, "/", i5, c1 / i5);
}

static void mpfr_interval_trans() {
    fi i1(1.0, 2.0);
    fi i2(3.0, 4.0);
    fi i3(-10.0, -5.0);
    fi i4(-3.0, +4.0);
    fi i5(5.0, 8.0);
    fi oi1(1.0, 2.0);
    fi oi2(3.0, 4.0);
    fi oi3(-10.0, -5.0);
    fi oi4(-3.0, +4.0);
    fi oi5(5.0, 8.0);
    oi1.set_is_lower_open(true); oi1.set_is_upper_open(true);
    oi2.set_is_lower_open(true); oi2.set_is_upper_open(true);
    oi3.set_is_lower_open(true); oi3.set_is_upper_open(true);
    oi4.set_is_lower_open(true); oi4.set_is_upper_open(true);
    oi5.set_is_lower_open(true); oi5.set_is_upper_open(true);

    fi inf;
    fi ozero_pinf;
    fi ozero_ninf;
    ozero_pinf.set_is_lower_inf(false);
    ozero_ninf.set_is_upper_inf(false);
    fi czero_pinf;
    fi czero_ninf;
    czero_pinf.set_is_lower_inf(false);
    czero_pinf.set_is_lower_open(false);
    czero_ninf.set_is_upper_inf(false);
    czero_ninf.set_is_upper_open(false);

    mpfp c1(0.6);
    mpfp c2(3.0);
    mpfp c3(0.0);
    mpfp c4(-4.5);
    mpfp c5(-0.3);

    std::cout << "=====================" << std::endl;
    std::cout << "power" << "(" << i1 << ", " << 3 << ") = " << power(i1, 3) << std::endl;
    std::cout << "power" << "(" << i2 << ", " << 3 << ") = " << power(i2, 3) << std::endl;
    std::cout << "power" << "(" << i3 << ", " << 3 << ") = " << power(i3, 3) << std::endl;
    std::cout << "power" << "(" << i4 << ", " << 3 << ") = " << power(i4, 3) << std::endl;
    std::cout << "power" << "(" << i5 << ", " << 3 << ") = " << power(i5, 3) << std::endl;
    std::cout << "power" << "(" << oi1 << ", " << 3 << ") = " << power(oi1, 3) << std::endl;
    std::cout << "power" << "(" << oi2 << ", " << 3 << ") = " << power(oi2, 3) << std::endl;
    std::cout << "power" << "(" << oi3 << ", " << 3 << ") = " << power(oi3, 3) << std::endl;
    std::cout << "power" << "(" << oi4 << ", " << 3 << ") = " << power(oi4, 3) << std::endl;
    std::cout << "power" << "(" << oi5 << ", " << 3 << ") = " << power(oi5, 3) << std::endl;
    std::cout << "power" << "(" << inf << ", " << 3 << ") = " << power(inf, 3) << std::endl;
    std::cout << "power" << "(" << ozero_ninf << ", " << 3 << ") = " << power(ozero_ninf, 3) << std::endl;
    std::cout << "power" << "(" << ozero_pinf << ", " << 3 << ") = " << power(ozero_pinf, 3) << std::endl;
    std::cout << "power" << "(" << czero_ninf << ", " << 3 << ") = " << power(czero_ninf, 3) << std::endl;
    std::cout << "power" << "(" << czero_pinf << ", " << 3 << ") = " << power(czero_pinf, 3) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "exp" << "(" << i1 << ") = " << exp(i1) << std::endl;
    std::cout << "exp" << "(" << i2 << ") = " << exp(i2) << std::endl;
    std::cout << "exp" << "(" << i3 << ") = " << exp(i3) << std::endl;
    std::cout << "exp" << "(" << i4 << ") = " << exp(i4) << std::endl;
    std::cout << "exp" << "(" << i5 << ") = " << exp(i5) << std::endl;
    std::cout << "exp" << "(" << oi1 << ") = " << exp(oi1) << std::endl;
    std::cout << "exp" << "(" << oi2 << ") = " << exp(oi2) << std::endl;
    std::cout << "exp" << "(" << oi3 << ") = " << exp(oi3) << std::endl;
    std::cout << "exp" << "(" << oi4 << ") = " << exp(oi4) << std::endl;
    std::cout << "exp" << "(" << oi5 << ") = " << exp(oi5) << std::endl;
    std::cout << "exp" << "(" << ozero_pinf << ") = " << exp(ozero_pinf) << std::endl;
    std::cout << "exp" << "(" << ozero_ninf << ") = " << exp(ozero_ninf) << std::endl;
    std::cout << "exp" << "(" << czero_pinf << ") = " << exp(czero_pinf) << std::endl;
    std::cout << "exp" << "(" << czero_ninf << ") = " << exp(czero_ninf) << std::endl;
    std::cout << "exp" << "(" << inf        << ") = " << exp(inf) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "exp2" << "(" << i1 << ") = " << exp2(i1) << std::endl;
    std::cout << "exp2" << "(" << i2 << ") = " << exp2(i2) << std::endl;
    std::cout << "exp2" << "(" << i3 << ") = " << exp2(i3) << std::endl;
    std::cout << "exp2" << "(" << i4 << ") = " << exp2(i4) << std::endl;
    std::cout << "exp2" << "(" << i5 << ") = " << exp2(i5) << std::endl;
    std::cout << "exp2" << "(" << oi1 << ") = " << exp2(oi1) << std::endl;
    std::cout << "exp2" << "(" << oi2 << ") = " << exp2(oi2) << std::endl;
    std::cout << "exp2" << "(" << oi3 << ") = " << exp2(oi3) << std::endl;
    std::cout << "exp2" << "(" << oi4 << ") = " << exp2(oi4) << std::endl;
    std::cout << "exp2" << "(" << oi5 << ") = " << exp2(oi5) << std::endl;
    std::cout << "exp2" << "(" << ozero_pinf << ") = " << exp2(ozero_pinf) << std::endl;
    std::cout << "exp2" << "(" << ozero_ninf << ") = " << exp2(ozero_ninf) << std::endl;
    std::cout << "exp2" << "(" << czero_pinf << ") = " << exp2(czero_pinf) << std::endl;
    std::cout << "exp2" << "(" << czero_ninf << ") = " << exp2(czero_ninf) << std::endl;
    std::cout << "exp2" << "(" << inf        << ") = " << exp2(inf) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "exp10" << "(" << i1 << ") = " << exp10(i1) << std::endl;
    std::cout << "exp10" << "(" << i2 << ") = " << exp10(i2) << std::endl;
    std::cout << "exp10" << "(" << i3 << ") = " << exp10(i3) << std::endl;
    std::cout << "exp10" << "(" << i4 << ") = " << exp10(i4) << std::endl;
    std::cout << "exp10" << "(" << i5 << ") = " << exp10(i5) << std::endl;
    std::cout << "exp10" << "(" << oi1 << ") = " << exp10(oi1) << std::endl;
    std::cout << "exp10" << "(" << oi2 << ") = " << exp10(oi2) << std::endl;
    std::cout << "exp10" << "(" << oi3 << ") = " << exp10(oi3) << std::endl;
    std::cout << "exp10" << "(" << oi4 << ") = " << exp10(oi4) << std::endl;
    std::cout << "exp10" << "(" << oi5 << ") = " << exp10(oi5) << std::endl;
    std::cout << "exp10" << "(" << ozero_pinf << ") = " << exp10(ozero_pinf) << std::endl;
    std::cout << "exp10" << "(" << ozero_ninf << ") = " << exp10(ozero_ninf) << std::endl;
    std::cout << "exp10" << "(" << czero_pinf << ") = " << exp10(czero_pinf) << std::endl;
    std::cout << "exp10" << "(" << czero_ninf << ") = " << exp10(czero_ninf) << std::endl;
    std::cout << "exp10" << "(" << inf        << ") = " << exp10(inf) << std::endl;


    std::cout << "=====================" << std::endl;
    std::cout << "log" << "(" << i1 << ") = " << log(i1) << std::endl;
    std::cout << "log" << "(" << i2 << ") = " << log(i2) << std::endl;
    std::cout << "log" << "(" << i5 << ") = " << log(i5) << std::endl;
    std::cout << "log" << "(" << oi1 << ") = " << log(oi1) << std::endl;
    std::cout << "log" << "(" << oi2 << ") = " << log(oi2) << std::endl;
    std::cout << "log" << "(" << oi5 << ") = " << log(oi5) << std::endl;
    std::cout << "log" << "(" << ozero_pinf << ") = " << log(ozero_pinf) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "log2" << "(" << i1 << ") = " << log2(i1) << std::endl;
    std::cout << "log2" << "(" << i2 << ") = " << log2(i2) << std::endl;
    std::cout << "log2" << "(" << i5 << ") = " << log2(i5) << std::endl;
    std::cout << "log2" << "(" << oi1 << ") = " << log2(oi1) << std::endl;
    std::cout << "log2" << "(" << oi2 << ") = " << log2(oi2) << std::endl;
    std::cout << "log2" << "(" << oi5 << ") = " << log2(oi5) << std::endl;
    std::cout << "log2" << "(" << ozero_pinf << ") = " << log2(ozero_pinf) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "log10" << "(" << i1 << ") = " << log10(i1) << std::endl;
    std::cout << "log10" << "(" << i2 << ") = " << log10(i2) << std::endl;
    std::cout << "log10" << "(" << i5 << ") = " << log10(i5) << std::endl;
    std::cout << "log10" << "(" << oi1 << ") = " << log10(oi1) << std::endl;
    std::cout << "log10" << "(" << oi2 << ") = " << log10(oi2) << std::endl;
    std::cout << "log10" << "(" << oi5 << ") = " << log10(oi5) << std::endl;
    std::cout << "log10" << "(" << ozero_pinf << ") = " << log10(ozero_pinf) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "sin" << "(" << i1 << ") = " << sin(i1) << std::endl;
    std::cout << "sin" << "(" << i2 << ") = " << sin(i2) << std::endl;
    std::cout << "sin" << "(" << i3 << ") = " << sin(i3) << std::endl;
    std::cout << "sin" << "(" << i4 << ") = " << sin(i4) << std::endl;
    std::cout << "sin" << "(" << i5 << ") = " << sin(i5) << std::endl;
    std::cout << "sin" << "(" << oi1 << ") = " << sin(oi1) << std::endl;
    std::cout << "sin" << "(" << oi2 << ") = " << sin(oi2) << std::endl;
    std::cout << "sin" << "(" << oi3 << ") = " << sin(oi3) << std::endl;
    std::cout << "sin" << "(" << oi4 << ") = " << sin(oi4) << std::endl;
    std::cout << "sin" << "(" << oi5 << ") = " << sin(oi5) << std::endl;
    std::cout << "sin" << "(" << ozero_pinf << ") = " << sin(ozero_pinf) << std::endl;
    std::cout << "sin" << "(" << ozero_ninf << ") = " << sin(ozero_ninf) << std::endl;
    std::cout << "sin" << "(" << czero_pinf << ") = " << sin(czero_pinf) << std::endl;
    std::cout << "sin" << "(" << czero_ninf << ") = " << sin(czero_ninf) << std::endl;
    std::cout << "sin" << "(" << inf        << ") = " << sin(inf) << std::endl;

    std::cout << "=====================" << std::endl;
    std::cout << "cos" << "(" << i1 << ") = " << cos(i1) << std::endl;
    std::cout << "cos" << "(" << i2 << ") = " << cos(i2) << std::endl;
    std::cout << "cos" << "(" << i3 << ") = " << cos(i3) << std::endl;
    std::cout << "cos" << "(" << i4 << ") = " << cos(i4) << std::endl;
    std::cout << "cos" << "(" << i5 << ") = " << cos(i5) << std::endl;
    std::cout << "cos" << "(" << oi1 << ") = " << cos(oi1) << std::endl;
    std::cout << "cos" << "(" << oi2 << ") = " << cos(oi2) << std::endl;
    std::cout << "cos" << "(" << oi3 << ") = " << cos(oi3) << std::endl;
    std::cout << "cos" << "(" << oi4 << ") = " << cos(oi4) << std::endl;
    std::cout << "cos" << "(" << oi5 << ") = " << cos(oi5) << std::endl;
    std::cout << "cos" << "(" << ozero_pinf << ") = " << cos(ozero_pinf) << std::endl;
    std::cout << "cos" << "(" << ozero_ninf << ") = " << cos(ozero_ninf) << std::endl;
    std::cout << "cos" << "(" << czero_pinf << ") = " << cos(czero_pinf) << std::endl;
    std::cout << "cos" << "(" << czero_ninf << ") = " << cos(czero_ninf) << std::endl;
    std::cout << "cos" << "(" << inf        << ") = " << cos(inf) << std::endl;
}

int main() {
    continue_on_violation(false);
    enable_trace("numerics");
    tst1();
    tst2();
    double_interval_trans();
    mpfr_interval_arith();
    mpfr_interval_inf1();
    mpfr_interval_inf2();
    mpfr_interval_trans();
    return has_violations() ? 1 : 0;
}
