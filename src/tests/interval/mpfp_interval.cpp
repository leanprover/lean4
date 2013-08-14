/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <vector>
#include "test.h"
#include "trace.h"
#include "double.h"
#include "mpfp.h"
#include "interval_def.h"

using namespace lean;

using std::cout;
using std::endl;

typedef interval<double> di;
typedef interval<mpfp> fi;

template<typename T1, typename T2, typename T3>
void print_result(T1 a, std::string const & op, T2 b, T3 r) {
    cout << a << " " << op << " " << b << " = " << r << endl;
}

static void mpfp_interval_arith() {
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

    cout << "=====================" << endl;
    print_result(i1, "+", c1, i1 + c1);
    print_result(i2, "+", c2, i2 + c2);
    print_result(i3, "+", c3, i3 + c3);
    print_result(i4, "+", c4, i4 + c4);
    print_result(i5, "+", c5, i5 + c5);
    print_result(i5, "+", c1, i5 + c1);
    print_result(i4, "+", c2, i4 + c2);
    print_result(i2, "+", c4, i2 + c4);
    print_result(i1, "+", c5, i1 + c5);

    cout << "=====================" << endl;
    print_result(c1, "+", i1, c1 + i1);
    print_result(c2, "+", i2, c2 + i2);
    print_result(c3, "+", i3, c3 + i3);
    print_result(c4, "+", i4, c4 + i4);
    print_result(c5, "+", i5, c5 + i5);
    print_result(c5, "+", i1, c5 + i1);
    print_result(c4, "+", i2, c4 + i2);
    print_result(c2, "+", i4, c2 + i4);
    print_result(c1, "+", i5, c1 + i5);

    cout << "=====================" << endl;
    print_result(i1, "-", c1, i1 - c1);
    print_result(i2, "-", c2, i2 - c2);
    print_result(i3, "-", c3, i3 - c3);
    print_result(i4, "-", c4, i4 - c4);
    print_result(i5, "-", c5, i5 - c5);
    print_result(i5, "-", c1, i5 - c1);
    print_result(i4, "-", c2, i4 - c2);
    print_result(i2, "-", c4, i2 - c4);
    print_result(i1, "-", c5, i1 - c5);

    cout << "=====================" << endl;
    print_result(c1, "-", i1, c1 - i1);
    print_result(c2, "-", i2, c2 - i2);
    print_result(c3, "-", i3, c3 - i3);
    print_result(c4, "-", i4, c4 - i4);
    print_result(c5, "-", i5, c5 - i5);
    print_result(c5, "-", i1, c5 - i1);
    print_result(c4, "-", i2, c4 - i2);
    print_result(c2, "-", i4, c2 - i4);
    print_result(c1, "-", i5, c1 - i5);

    cout << "=====================" << endl;
    print_result(i1, "*", c1, i1 * c1);
    print_result(i2, "*", c2, i2 * c2);
    print_result(i3, "*", c3, i3 * c3);
    print_result(i4, "*", c4, i4 * c4);
    print_result(i5, "*", c5, i5 * c5);
    print_result(i5, "*", c1, i5 * c1);
    print_result(i4, "*", c2, i4 * c2);
    print_result(i2, "*", c4, i2 * c4);
    print_result(i1, "*", c5, i1 * c5);

    cout << "=====================" << endl;
    print_result(c1, "*", i1, c1 * i1);
    print_result(c2, "*", i2, c2 * i2);
    print_result(c3, "*", i3, c3 * i3);
    print_result(c4, "*", i4, c4 * i4);
    print_result(c5, "*", i5, c5 * i5);
    print_result(c5, "*", i1, c5 * i1);
    print_result(c4, "*", i2, c4 * i2);
    print_result(c2, "*", i4, c2 * i4);
    print_result(c1, "*", i5, c1 * i5);

    cout << "=====================" << endl;
    print_result(i1, "/", c1, i1 / c1);
    print_result(i2, "/", c2, i2 / c2);
    print_result(i3, "/", c3, i3 / c3);
    print_result(i4, "/", c4, i4 / c4);
    print_result(i5, "/", c5, i5 / c5);
    print_result(i5, "/", c1, i5 / c1);
    print_result(i4, "/", c2, i4 / c2);
    print_result(i2, "/", c4, i2 / c4);
    print_result(i1, "/", c5, i1 / c5);

    cout << "=====================" << endl;
    print_result(c1, "/", i1, c1 / i1);
    print_result(c2, "/", i2, c2 / i2);
    print_result(c3, "/", i3, c3 / i3);
    print_result(c5, "/", i5, c5 / i5);
    print_result(c5, "/", i1, c5 / i1);
    print_result(c4, "/", i2, c4 / i2);
    print_result(c1, "/", i5, c1 / i5);
}

static void mpfp_interval_inf1() {
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

    cout << i1 << " * " << ozero_ninf << " = " << i1 * ozero_ninf << endl;
    cout << i1 << " * " << ozero_pinf << " = " << i1 * ozero_pinf << endl;
    cout << i1 << " * " << czero_ninf << " = " << i1 * czero_ninf << endl;
    cout << i1 << " * " << czero_pinf << " = " << i1 * czero_pinf << endl;
    lean_assert(i1 * ozero_ninf == ozero_ninf); lean_assert(ozero_ninf * i1 == ozero_ninf);
    lean_assert(i1 * ozero_pinf == ozero_pinf); lean_assert(ozero_pinf * i1 == ozero_pinf);
    lean_assert(i1 * czero_ninf == czero_ninf); lean_assert(czero_ninf * i1 == czero_ninf);
    lean_assert(i1 * czero_pinf == czero_pinf); lean_assert(czero_pinf * i1 == czero_pinf);

    cout << "=== Addition between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << endl;
    cout << ozero_ninf << " + " << ozero_ninf << " = " << ozero_ninf + ozero_ninf << endl;
    cout << ozero_ninf << " + " << ozero_pinf << " = " << ozero_ninf + ozero_pinf << endl;
    cout << ozero_ninf << " + " << czero_ninf << " = " << ozero_ninf + czero_ninf << endl;
    cout << ozero_ninf << " + " << czero_pinf << " = " << ozero_ninf + czero_pinf << endl;
    cout << ozero_pinf << " + " << ozero_ninf << " = " << ozero_pinf + ozero_ninf << endl;
    cout << ozero_pinf << " + " << ozero_pinf << " = " << ozero_pinf + ozero_pinf << endl;
    cout << ozero_pinf << " + " << czero_ninf << " = " << ozero_pinf + czero_ninf << endl;
    cout << ozero_pinf << " + " << czero_pinf << " = " << ozero_pinf + czero_pinf << endl;
    cout << czero_ninf << " + " << ozero_ninf << " = " << czero_ninf + ozero_ninf << endl;
    cout << czero_ninf << " + " << ozero_pinf << " = " << czero_ninf + ozero_pinf << endl;
    cout << czero_ninf << " + " << czero_ninf << " = " << czero_ninf + czero_ninf << endl;
    cout << czero_ninf << " + " << czero_pinf << " = " << czero_ninf + czero_pinf << endl;
    cout << czero_pinf << " + " << ozero_ninf << " = " << czero_pinf + ozero_ninf << endl;
    cout << czero_pinf << " + " << ozero_pinf << " = " << czero_pinf + ozero_pinf << endl;
    cout << czero_pinf << " + " << czero_ninf << " = " << czero_pinf + czero_ninf << endl;
    cout << czero_pinf << " + " << czero_pinf << " = " << czero_pinf + czero_pinf << endl;

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

    cout << "=== Subtraction between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << endl;
    cout << ozero_ninf << " - " << ozero_ninf << " = " << ozero_ninf - ozero_ninf << endl;
    cout << ozero_ninf << " - " << ozero_pinf << " = " << ozero_ninf - ozero_pinf << endl;
    cout << ozero_ninf << " - " << czero_ninf << " = " << ozero_ninf - czero_ninf << endl;
    cout << ozero_ninf << " - " << czero_pinf << " = " << ozero_ninf - czero_pinf << endl;
    cout << ozero_pinf << " - " << ozero_ninf << " = " << ozero_pinf - ozero_ninf << endl;
    cout << ozero_pinf << " - " << ozero_pinf << " = " << ozero_pinf - ozero_pinf << endl;
    cout << ozero_pinf << " - " << czero_ninf << " = " << ozero_pinf - czero_ninf << endl;
    cout << ozero_pinf << " - " << czero_pinf << " = " << ozero_pinf - czero_pinf << endl;
    cout << czero_ninf << " - " << ozero_ninf << " = " << czero_ninf - ozero_ninf << endl;
    cout << czero_ninf << " - " << ozero_pinf << " = " << czero_ninf - ozero_pinf << endl;
    cout << czero_ninf << " - " << czero_ninf << " = " << czero_ninf - czero_ninf << endl;
    cout << czero_ninf << " - " << czero_pinf << " = " << czero_ninf - czero_pinf << endl;
    cout << czero_pinf << " - " << ozero_ninf << " = " << czero_pinf - ozero_ninf << endl;
    cout << czero_pinf << " - " << ozero_pinf << " = " << czero_pinf - ozero_pinf << endl;
    cout << czero_pinf << " - " << czero_ninf << " = " << czero_pinf - czero_ninf << endl;
    cout << czero_pinf << " - " << czero_pinf << " = " << czero_pinf - czero_pinf << endl;

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

    cout << "=== Multiplication between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << endl;
    cout << ozero_ninf << " * " << ozero_ninf << " = " << ozero_ninf * ozero_ninf << endl;
    cout << ozero_ninf << " * " << ozero_pinf << " = " << ozero_ninf * ozero_pinf << endl;
    cout << ozero_ninf << " * " << czero_ninf << " = " << ozero_ninf * czero_ninf << endl;
    cout << ozero_ninf << " * " << czero_pinf << " = " << ozero_ninf * czero_pinf << endl;
    cout << ozero_pinf << " * " << ozero_ninf << " = " << ozero_pinf * ozero_ninf << endl;
    cout << ozero_pinf << " * " << ozero_pinf << " = " << ozero_pinf * ozero_pinf << endl;
    cout << ozero_pinf << " * " << czero_ninf << " = " << ozero_pinf * czero_ninf << endl;
    cout << ozero_pinf << " * " << czero_pinf << " = " << ozero_pinf * czero_pinf << endl;
    cout << czero_ninf << " * " << ozero_ninf << " = " << czero_ninf * ozero_ninf << endl;
    cout << czero_ninf << " * " << ozero_pinf << " = " << czero_ninf * ozero_pinf << endl;
    cout << czero_ninf << " * " << czero_ninf << " = " << czero_ninf * czero_ninf << endl;
    cout << czero_ninf << " * " << czero_pinf << " = " << czero_ninf * czero_pinf << endl;
    cout << czero_pinf << " * " << ozero_ninf << " = " << czero_pinf * ozero_ninf << endl;
    cout << czero_pinf << " * " << ozero_pinf << " = " << czero_pinf * ozero_pinf << endl;
    cout << czero_pinf << " * " << czero_ninf << " = " << czero_pinf * czero_ninf << endl;
    cout << czero_pinf << " * " << czero_pinf << " = " << czero_pinf * czero_pinf << endl;

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

    cout << "=== Division between [0, +oo), (-oo, 0], (0, +oo), (-oo, 0) ===" << endl;
    cout << ozero_ninf << " / " << ozero_ninf << " = " << ozero_ninf / ozero_ninf << endl;
    cout << ozero_ninf << " / " << ozero_pinf << " = " << ozero_ninf / ozero_pinf << endl;
    cout << ozero_pinf << " / " << ozero_ninf << " = " << ozero_pinf / ozero_ninf << endl;
    cout << ozero_pinf << " / " << ozero_pinf << " = " << ozero_pinf / ozero_pinf << endl;
    cout << czero_ninf << " / " << ozero_ninf << " = " << czero_ninf / ozero_ninf << endl;
    cout << czero_ninf << " / " << ozero_pinf << " = " << czero_ninf / ozero_pinf << endl;
    cout << czero_pinf << " / " << ozero_ninf << " = " << czero_pinf / ozero_ninf << endl;
    cout << czero_pinf << " / " << ozero_pinf << " = " << czero_pinf / ozero_pinf << endl;

    lean_assert(ozero_ninf / ozero_ninf == ozero_pinf);
    lean_assert(ozero_ninf / ozero_pinf == ozero_ninf);
    lean_assert(ozero_pinf / ozero_ninf == ozero_ninf);
    lean_assert(ozero_pinf / ozero_pinf == ozero_pinf);
    lean_assert(czero_ninf / ozero_ninf == czero_pinf);
    lean_assert(czero_ninf / ozero_pinf == czero_ninf);
    lean_assert(czero_pinf / ozero_ninf == czero_ninf);
    lean_assert(czero_pinf / ozero_pinf == czero_pinf);
}

static void mpfp_interval_inf2() {
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

static void mpfp_interval_trans() {
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

    cout << "=====================" << endl;
    cout << "power" << "(" << i1 << ", " << 3 << ") = " << power(i1, 3) << endl;
    cout << "power" << "(" << i2 << ", " << 3 << ") = " << power(i2, 3) << endl;
    cout << "power" << "(" << i3 << ", " << 3 << ") = " << power(i3, 3) << endl;
    cout << "power" << "(" << i4 << ", " << 3 << ") = " << power(i4, 3) << endl;
    cout << "power" << "(" << i5 << ", " << 3 << ") = " << power(i5, 3) << endl;
    cout << "power" << "(" << oi1 << ", " << 3 << ") = " << power(oi1, 3) << endl;
    cout << "power" << "(" << oi2 << ", " << 3 << ") = " << power(oi2, 3) << endl;
    cout << "power" << "(" << oi3 << ", " << 3 << ") = " << power(oi3, 3) << endl;
    cout << "power" << "(" << oi4 << ", " << 3 << ") = " << power(oi4, 3) << endl;
    cout << "power" << "(" << oi5 << ", " << 3 << ") = " << power(oi5, 3) << endl;
    cout << "power" << "(" << inf << ", " << 3 << ") = " << power(inf, 3) << endl;
    cout << "power" << "(" << ozero_ninf << ", " << 3 << ") = " << power(ozero_ninf, 3) << endl;
    cout << "power" << "(" << ozero_pinf << ", " << 3 << ") = " << power(ozero_pinf, 3) << endl;
    cout << "power" << "(" << czero_ninf << ", " << 3 << ") = " << power(czero_ninf, 3) << endl;
    cout << "power" << "(" << czero_pinf << ", " << 3 << ") = " << power(czero_pinf, 3) << endl;

    cout << "=====================" << endl;
    cout << "exp" << "(" << i1 << ") = " << exp(i1) << endl;
    cout << "exp" << "(" << i2 << ") = " << exp(i2) << endl;
    cout << "exp" << "(" << i3 << ") = " << exp(i3) << endl;
    cout << "exp" << "(" << i4 << ") = " << exp(i4) << endl;
    cout << "exp" << "(" << i5 << ") = " << exp(i5) << endl;
    cout << "exp" << "(" << oi1 << ") = " << exp(oi1) << endl;
    cout << "exp" << "(" << oi2 << ") = " << exp(oi2) << endl;
    cout << "exp" << "(" << oi3 << ") = " << exp(oi3) << endl;
    cout << "exp" << "(" << oi4 << ") = " << exp(oi4) << endl;
    cout << "exp" << "(" << oi5 << ") = " << exp(oi5) << endl;
    cout << "exp" << "(" << ozero_pinf << ") = " << exp(ozero_pinf) << endl;
    cout << "exp" << "(" << ozero_ninf << ") = " << exp(ozero_ninf) << endl;
    cout << "exp" << "(" << czero_pinf << ") = " << exp(czero_pinf) << endl;
    cout << "exp" << "(" << czero_ninf << ") = " << exp(czero_ninf) << endl;
    cout << "exp" << "(" << inf        << ") = " << exp(inf) << endl;

    cout << "=====================" << endl;
    cout << "exp2" << "(" << i1 << ") = " << exp2(i1) << endl;
    cout << "exp2" << "(" << i2 << ") = " << exp2(i2) << endl;
    cout << "exp2" << "(" << i3 << ") = " << exp2(i3) << endl;
    cout << "exp2" << "(" << i4 << ") = " << exp2(i4) << endl;
    cout << "exp2" << "(" << i5 << ") = " << exp2(i5) << endl;
    cout << "exp2" << "(" << oi1 << ") = " << exp2(oi1) << endl;
    cout << "exp2" << "(" << oi2 << ") = " << exp2(oi2) << endl;
    cout << "exp2" << "(" << oi3 << ") = " << exp2(oi3) << endl;
    cout << "exp2" << "(" << oi4 << ") = " << exp2(oi4) << endl;
    cout << "exp2" << "(" << oi5 << ") = " << exp2(oi5) << endl;
    cout << "exp2" << "(" << ozero_pinf << ") = " << exp2(ozero_pinf) << endl;
    cout << "exp2" << "(" << ozero_ninf << ") = " << exp2(ozero_ninf) << endl;
    cout << "exp2" << "(" << czero_pinf << ") = " << exp2(czero_pinf) << endl;
    cout << "exp2" << "(" << czero_ninf << ") = " << exp2(czero_ninf) << endl;
    cout << "exp2" << "(" << inf        << ") = " << exp2(inf) << endl;

    cout << "=====================" << endl;
    cout << "exp10" << "(" << i1 << ") = " << exp10(i1) << endl;
    cout << "exp10" << "(" << i2 << ") = " << exp10(i2) << endl;
    cout << "exp10" << "(" << i3 << ") = " << exp10(i3) << endl;
    cout << "exp10" << "(" << i4 << ") = " << exp10(i4) << endl;
    cout << "exp10" << "(" << i5 << ") = " << exp10(i5) << endl;
    cout << "exp10" << "(" << oi1 << ") = " << exp10(oi1) << endl;
    cout << "exp10" << "(" << oi2 << ") = " << exp10(oi2) << endl;
    cout << "exp10" << "(" << oi3 << ") = " << exp10(oi3) << endl;
    cout << "exp10" << "(" << oi4 << ") = " << exp10(oi4) << endl;
    cout << "exp10" << "(" << oi5 << ") = " << exp10(oi5) << endl;
    cout << "exp10" << "(" << ozero_pinf << ") = " << exp10(ozero_pinf) << endl;
    cout << "exp10" << "(" << ozero_ninf << ") = " << exp10(ozero_ninf) << endl;
    cout << "exp10" << "(" << czero_pinf << ") = " << exp10(czero_pinf) << endl;
    cout << "exp10" << "(" << czero_ninf << ") = " << exp10(czero_ninf) << endl;
    cout << "exp10" << "(" << inf        << ") = " << exp10(inf) << endl;

    cout << "=====================" << endl;
    cout << "log" << "(" << i1 << ") = " << log(i1) << endl;
    cout << "log" << "(" << i2 << ") = " << log(i2) << endl;
    cout << "log" << "(" << i5 << ") = " << log(i5) << endl;
    cout << "log" << "(" << oi1 << ") = " << log(oi1) << endl;
    cout << "log" << "(" << oi2 << ") = " << log(oi2) << endl;
    cout << "log" << "(" << oi5 << ") = " << log(oi5) << endl;
    cout << "log" << "(" << ozero_pinf << ") = " << log(ozero_pinf) << endl;

    cout << "=====================" << endl;
    cout << "log2" << "(" << i1 << ") = " << log2(i1) << endl;
    cout << "log2" << "(" << i2 << ") = " << log2(i2) << endl;
    cout << "log2" << "(" << i5 << ") = " << log2(i5) << endl;
    cout << "log2" << "(" << oi1 << ") = " << log2(oi1) << endl;
    cout << "log2" << "(" << oi2 << ") = " << log2(oi2) << endl;
    cout << "log2" << "(" << oi5 << ") = " << log2(oi5) << endl;
    cout << "log2" << "(" << ozero_pinf << ") = " << log2(ozero_pinf) << endl;

    cout << "=====================" << endl;
    cout << "log10" << "(" << i1 << ") = " << log10(i1) << endl;
    cout << "log10" << "(" << i2 << ") = " << log10(i2) << endl;
    cout << "log10" << "(" << i5 << ") = " << log10(i5) << endl;
    cout << "log10" << "(" << oi1 << ") = " << log10(oi1) << endl;
    cout << "log10" << "(" << oi2 << ") = " << log10(oi2) << endl;
    cout << "log10" << "(" << oi5 << ") = " << log10(oi5) << endl;
    cout << "log10" << "(" << ozero_pinf << ") = " << log10(ozero_pinf) << endl;

    cout << "=====================" << endl;
    cout << "sin" << "(" << i1 << ") = " << sin(i1) << endl;
    cout << "sin" << "(" << i2 << ") = " << sin(i2) << endl;
    cout << "sin" << "(" << i3 << ") = " << sin(i3) << endl;
    cout << "sin" << "(" << i4 << ") = " << sin(i4) << endl;
    cout << "sin" << "(" << i5 << ") = " << sin(i5) << endl;
    cout << "sin" << "(" << oi1 << ") = " << sin(oi1) << endl;
    cout << "sin" << "(" << oi2 << ") = " << sin(oi2) << endl;
    cout << "sin" << "(" << oi3 << ") = " << sin(oi3) << endl;
    cout << "sin" << "(" << oi4 << ") = " << sin(oi4) << endl;
    cout << "sin" << "(" << oi5 << ") = " << sin(oi5) << endl;
    cout << "sin" << "(" << ozero_pinf << ") = " << sin(ozero_pinf) << endl;
    cout << "sin" << "(" << ozero_ninf << ") = " << sin(ozero_ninf) << endl;
    cout << "sin" << "(" << czero_pinf << ") = " << sin(czero_pinf) << endl;
    cout << "sin" << "(" << czero_ninf << ") = " << sin(czero_ninf) << endl;
    cout << "sin" << "(" << inf        << ") = " << sin(inf) << endl;

    cout << "=====================" << endl;
    cout << "cos" << "(" << i1 << ") = " << cos(i1) << endl;
    cout << "cos" << "(" << i2 << ") = " << cos(i2) << endl;
    cout << "cos" << "(" << i3 << ") = " << cos(i3) << endl;
    cout << "cos" << "(" << i4 << ") = " << cos(i4) << endl;
    cout << "cos" << "(" << i5 << ") = " << cos(i5) << endl;
    cout << "cos" << "(" << oi1 << ") = " << cos(oi1) << endl;
    cout << "cos" << "(" << oi2 << ") = " << cos(oi2) << endl;
    cout << "cos" << "(" << oi3 << ") = " << cos(oi3) << endl;
    cout << "cos" << "(" << oi4 << ") = " << cos(oi4) << endl;
    cout << "cos" << "(" << oi5 << ") = " << cos(oi5) << endl;
    cout << "cos" << "(" << ozero_pinf << ") = " << cos(ozero_pinf) << endl;
    cout << "cos" << "(" << ozero_ninf << ") = " << cos(ozero_ninf) << endl;
    cout << "cos" << "(" << czero_pinf << ") = " << cos(czero_pinf) << endl;
    cout << "cos" << "(" << czero_ninf << ") = " << cos(czero_ninf) << endl;
    cout << "cos" << "(" << inf        << ") = " << cos(inf) << endl;

    cout << "=====================" << endl;
    cout << "tan" << "(" << i1 << ") = " << tan(i1) << endl;
    cout << "tan" << "(" << i2 << ") = " << tan(i2) << endl;
    cout << "tan" << "(" << i3 << ") = " << tan(i3) << endl;
    cout << "tan" << "(" << i4 << ") = " << tan(i4) << endl;
    cout << "tan" << "(" << i5 << ") = " << tan(i5) << endl;
    cout << "tan" << "(" << oi1 << ") = " << tan(oi1) << endl;
    cout << "tan" << "(" << oi2 << ") = " << tan(oi2) << endl;
    cout << "tan" << "(" << oi3 << ") = " << tan(oi3) << endl;
    cout << "tan" << "(" << oi4 << ") = " << tan(oi4) << endl;
    cout << "tan" << "(" << oi5 << ") = " << tan(oi5) << endl;
    cout << "tan" << "(" << ozero_pinf << ") = " << tan(ozero_pinf) << endl;
    cout << "tan" << "(" << ozero_ninf << ") = " << tan(ozero_ninf) << endl;
    cout << "tan" << "(" << czero_pinf << ") = " << tan(czero_pinf) << endl;
    cout << "tan" << "(" << czero_ninf << ") = " << tan(czero_ninf) << endl;
    cout << "tan" << "(" << inf        << ") = " << tan(inf) << endl;
}

int main() {
    continue_on_violation(true);
    enable_trace("numerics");
    mpfp_interval_arith();
    mpfp_interval_inf1();
    mpfp_interval_inf2();
    mpfp_interval_trans();
    return has_violations() ? 1 : 0;
}
