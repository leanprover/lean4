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


// Check F(I.lower()) \in F(I) and F(I.upper()) \in F(I).
#define check_bop(f, i, c) {                                            \
        cout << #f << "(" << #i << " " << i << ", " << c << ") = ";     \
        fi tmp = f(i, c);                                               \
        cout << tmp << endl;                                            \
        if(!i.is_lower_inf()) {                                         \
            numeric_traits<mpfp>::set_rounding(false);                  \
            mpfp l = f(i.lower(), c);                                   \
            cout << "\t" << #f << "(" << i.lower() << ", " << c << ") = " << l << endl; \
            lean_assert(tmp.is_lower_inf() ||                           \
                        ((tmp.lower() <= l) && (tmp.is_upper_inf() || (l <= tmp.upper())))); \
        }                                                               \
        if(!i.is_upper_inf()) {                                         \
            numeric_traits<mpfp>::set_rounding(true);                   \
            mpfp u = f(i.upper(), c);                                   \
            cout << "\t" << #f << "(" << i.upper() << ", " << c << ") = " << u << endl; \
            lean_assert(tmp.is_upper_inf() ||                           \
                        ((tmp.is_lower_inf() || (tmp.lower() <= u)) && (u <= tmp.upper()))); \
        }                                                               \
}

#define check_uop(f, i) {                                               \
        cout << #f << "(" << #i << " " << i << ") = ";                  \
        fi tmp = f(i);                                                  \
        cout << tmp << endl;                                            \
        if(!i.is_lower_inf()) {                                         \
            numeric_traits<mpfp>::set_rounding(false);                  \
            mpfp l = f(i.lower());                                      \
            cout << "\t" << #f << "(" << i.lower() << ") = " << l << endl; \
            lean_assert(tmp.is_lower_inf() ||                           \
                        ((tmp.lower() <= l) && (tmp.is_upper_inf() || (l <= tmp.upper())))); \
        }                                                               \
        if(!i.is_upper_inf()) {                                         \
            numeric_traits<mpfp>::set_rounding(true);                   \
            mpfp u = f(i.upper());                                      \
            cout << "\t" << #f << "(" << i.upper() << ") = " << u << endl; \
            lean_assert(tmp.is_upper_inf() ||                           \
                        ((tmp.is_lower_inf() || (tmp.lower() <= u)) && (u <= tmp.upper()))); \
        }                                                               \
}

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
    fi i6(0.3, 1.67);
    fi i7(1.8, 3.5);
    fi i8(3.5, 4.9);
    fi i9(-3.15, -2.0);
    fi i10(-0.99, 0.5);
    fi i11(-0.8, -0.5);
    fi i12(-0.3, 0.2);
    fi i13(0.5, 0.9);
    fi i14(-0.1, 0.8);
    fi i15(-0.4, -0.3);

    fi oi1(1.0, 2.0);
    fi oi2(3.0, 4.0);
    fi oi3(-10.0, -5.0);
    fi oi4(-3.0, +4.0);
    fi oi5(5.0, 8.0);
    fi oi6(0.3, 1.67);
    fi oi7(1.8, 3.5);
    fi oi8(3.5, 4.9);
    fi oi9(-3.15, -2.0);
    fi oi10(-3.19, -1.0);
    fi oi11(-0.8, -0.5);
    fi oi12(-0.3, 0.2);
    fi oi13(0.5, 0.9);
    fi oi14(-0.1, 0.8);
    fi oi15(-0.4, -0.3);

    oi1.set_is_lower_open(true);  oi1.set_is_upper_open(true);
    oi2.set_is_lower_open(true);  oi2.set_is_upper_open(true);
    oi3.set_is_lower_open(true);  oi3.set_is_upper_open(true);
    oi4.set_is_lower_open(true);  oi4.set_is_upper_open(true);
    oi5.set_is_lower_open(true);  oi5.set_is_upper_open(true);
    oi6.set_is_lower_open(true);  oi6.set_is_upper_open(true);
    oi7.set_is_lower_open(true);  oi7.set_is_upper_open(true);
    oi8.set_is_lower_open(true);  oi8.set_is_upper_open(true);
    oi9.set_is_lower_open(true);  oi9.set_is_upper_open(true);
    oi10.set_is_lower_open(true); oi10.set_is_upper_open(true);
    oi11.set_is_lower_open(true); oi11.set_is_upper_open(true);
    oi12.set_is_lower_open(true); oi12.set_is_upper_open(true);
    oi13.set_is_lower_open(true); oi13.set_is_upper_open(true);
    oi14.set_is_lower_open(true); oi14.set_is_upper_open(true);
    oi15.set_is_lower_open(true); oi15.set_is_upper_open(true);

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
    check_bop(power, i1, 3lu);
    check_bop(power, i2, 3lu);
    check_bop(power, i3, 3lu);
    check_bop(power, i4, 3lu);
    check_bop(power, i5, 3lu);
    check_bop(power, i6, 3lu);
    check_bop(power, i7, 3lu);
    check_bop(power, i8, 3lu);
    check_bop(power, i9, 3lu);
    check_bop(power, i10, 3lu);
    check_bop(power, i11, 3lu);
    check_bop(power, i12, 3lu);
    check_bop(power, i13, 3lu);
    check_bop(power, i14, 3lu);
    check_bop(power, i15, 3lu);
    check_bop(power, oi1, 3lu);
    check_bop(power, oi2, 3lu);
    check_bop(power, oi3, 3lu);
    check_bop(power, oi4, 3lu);
    check_bop(power, oi5, 3lu);
    check_bop(power, oi6, 3lu);
    check_bop(power, oi7, 3lu);
    check_bop(power, oi8, 3lu);
    check_bop(power, oi9, 3lu);
    check_bop(power, oi10, 3lu);
    check_bop(power, oi11, 3lu);
    check_bop(power, oi12, 3lu);
    check_bop(power, oi13, 3lu);
    check_bop(power, oi14, 3lu);
    check_bop(power, oi15, 3lu);
    check_bop(power, inf, 3lu);
    check_bop(power, ozero_ninf, 3lu);
    check_bop(power, ozero_pinf, 3lu);
    check_bop(power, czero_ninf, 3lu);
    check_bop(power, czero_pinf, 3lu);

    cout << "=====================" << endl;
    check_uop(exp, i1);
    check_uop(exp, i2);
    check_uop(exp, i3);
    check_uop(exp, i4);
    check_uop(exp, i5);
    check_uop(exp, i6);
    check_uop(exp, i7);
    check_uop(exp, i8);
    check_uop(exp, i9);
    check_uop(exp, i10);
    check_uop(exp, i11);
    check_uop(exp, i12);
    check_uop(exp, i13);
    check_uop(exp, i14);
    check_uop(exp, i15);
    check_uop(exp, oi1);
    check_uop(exp, oi2);
    check_uop(exp, oi3);
    check_uop(exp, oi4);
    check_uop(exp, oi5);
    check_uop(exp, oi6);
    check_uop(exp, oi7);
    check_uop(exp, oi8);
    check_uop(exp, oi9);
    check_uop(exp, oi10);
    check_uop(exp, oi11);
    check_uop(exp, oi12);
    check_uop(exp, oi13);
    check_uop(exp, oi14);
    check_uop(exp, oi15);
    check_uop(exp, inf);
    check_uop(exp, ozero_pinf);
    check_uop(exp, ozero_ninf);
    check_uop(exp, czero_pinf);
    check_uop(exp, czero_ninf);

    cout << "=====================" << endl;
    check_uop(exp2, i1);
    check_uop(exp2, i2);
    check_uop(exp2, i3);
    check_uop(exp2, i4);
    check_uop(exp2, i5);
    check_uop(exp2, i6);
    check_uop(exp2, i7);
    check_uop(exp2, i8);
    check_uop(exp2, i9);
    check_uop(exp2, i10);
    check_uop(exp2, i11);
    check_uop(exp2, i12);
    check_uop(exp2, i13);
    check_uop(exp2, i14);
    check_uop(exp2, i15);
    check_uop(exp2, oi1);
    check_uop(exp2, oi2);
    check_uop(exp2, oi3);
    check_uop(exp2, oi4);
    check_uop(exp2, oi5);
    check_uop(exp2, oi6);
    check_uop(exp2, oi7);
    check_uop(exp2, oi8);
    check_uop(exp2, oi9);
    check_uop(exp2, oi10);
    check_uop(exp2, oi11);
    check_uop(exp2, oi12);
    check_uop(exp2, oi13);
    check_uop(exp2, oi14);
    check_uop(exp2, oi15);
    check_uop(exp2, inf);
    check_uop(exp2, ozero_pinf);
    check_uop(exp2, ozero_ninf);
    check_uop(exp2, czero_pinf);
    check_uop(exp2, czero_ninf);

    cout << "=====================" << endl;
    check_uop(exp10, i1);
    check_uop(exp10, i2);
    check_uop(exp10, i3);
    check_uop(exp10, i4);
    check_uop(exp10, i5);
    check_uop(exp10, i6);
    check_uop(exp10, i7);
    check_uop(exp10, i8);
    check_uop(exp10, i9);
    check_uop(exp10, i10);
    check_uop(exp10, i11);
    check_uop(exp10, i12);
    check_uop(exp10, i13);
    check_uop(exp10, i14);
    check_uop(exp10, i15);
    check_uop(exp10, oi1);
    check_uop(exp10, oi2);
    check_uop(exp10, oi3);
    check_uop(exp10, oi4);
    check_uop(exp10, oi5);
    check_uop(exp10, oi6);
    check_uop(exp10, oi7);
    check_uop(exp10, oi8);
    check_uop(exp10, oi9);
    check_uop(exp10, oi10);
    check_uop(exp10, oi11);
    check_uop(exp10, oi12);
    check_uop(exp10, oi13);
    check_uop(exp10, oi14);
    check_uop(exp10, oi15);
    check_uop(exp10, inf);
    check_uop(exp10, ozero_pinf);
    check_uop(exp10, ozero_ninf);
    check_uop(exp10, czero_pinf);
    check_uop(exp10, czero_ninf);

    cout << "=====================" << endl;
    check_uop(log, i1);
    check_uop(log, i2);
    check_uop(log, i5);
    check_uop(log, i6);
    check_uop(log, i7);
    check_uop(log, i8);
    check_uop(log, oi1);
    check_uop(log, oi2);
    check_uop(log, oi5);
    check_uop(log, oi6);
    check_uop(log, oi7);
    check_uop(log, oi8);
    check_uop(log, ozero_pinf);

    cout << "=====================" << endl;
    check_uop(log2, i1);
    check_uop(log2, i2);
    check_uop(log2, i5);
    check_uop(log2, i6);
    check_uop(log2, i7);
    check_uop(log2, i8);
    check_uop(log2, oi1);
    check_uop(log2, oi2);
    check_uop(log2, oi5);
    check_uop(log2, oi6);
    check_uop(log2, oi7);
    check_uop(log2, oi8);
    check_uop(log2, ozero_pinf);

    cout << "=====================" << endl;
    check_uop(log10, i1);
    check_uop(log10, i2);
    check_uop(log10, i5);
    check_uop(log10, i6);
    check_uop(log10, i7);
    check_uop(log10, i8);
    check_uop(log10, oi1);
    check_uop(log10, oi2);
    check_uop(log10, oi5);
    check_uop(log10, oi6);
    check_uop(log10, oi7);
    check_uop(log10, oi8);
    check_uop(log10, ozero_pinf);

    cout << "=====================" << endl;
    check_uop(sin, i1);
    check_uop(sin, i2);
    check_uop(sin, i3);
    check_uop(sin, i4);
    check_uop(sin, i5);
    check_uop(sin, i6);
    check_uop(sin, i7);
    check_uop(sin, i8);
    check_uop(sin, i9);
    check_uop(sin, i10);
    check_uop(sin, oi1);
    check_uop(sin, oi2);
    check_uop(sin, oi3);
    check_uop(sin, oi4);
    check_uop(sin, oi5);
    check_uop(sin, oi6);
    check_uop(sin, oi7);
    check_uop(sin, oi8);
    check_uop(sin, oi9);
    check_uop(sin, oi10);
    check_uop(sin, inf);
    check_uop(sin, ozero_pinf);
    check_uop(sin, ozero_ninf);
    check_uop(sin, czero_pinf);
    check_uop(sin, czero_ninf);

    cout << "=====================" << endl;
    check_uop(cos, i1);
    check_uop(cos, i2);
    check_uop(cos, i3);
    check_uop(cos, i4);
    check_uop(cos, i5);
    check_uop(cos, i6);
    check_uop(cos, i7);
    check_uop(cos, i8);
    check_uop(cos, i9);
    check_uop(cos, i10);
    check_uop(cos, oi1);
    check_uop(cos, oi2);
    check_uop(cos, oi3);
    check_uop(cos, oi4);
    check_uop(cos, oi5);
    check_uop(cos, oi6);
    check_uop(cos, oi7);
    check_uop(cos, oi8);
    check_uop(cos, oi9);
    check_uop(cos, oi10);
    check_uop(cos, inf);
    check_uop(cos, ozero_pinf);
    check_uop(cos, ozero_ninf);
    check_uop(cos, czero_pinf);
    check_uop(cos, czero_ninf);

    cout << "=====================" << endl;
    check_uop(tan, i1);
    check_uop(tan, i2);
    check_uop(tan, i3);
    check_uop(tan, i4);
    check_uop(tan, i5);
    check_uop(tan, i6);
    check_uop(tan, i7);
    check_uop(tan, i8);
    check_uop(tan, i9);
    check_uop(tan, i10);
    check_uop(tan, oi1);
    check_uop(tan, oi2);
    check_uop(tan, oi3);
    check_uop(tan, oi4);
    check_uop(tan, oi5);
    check_uop(tan, oi6);
    check_uop(tan, oi7);
    check_uop(tan, oi8);
    check_uop(tan, oi9);
    check_uop(tan, oi10);
    check_uop(tan, inf);
    check_uop(tan, ozero_pinf);
    check_uop(tan, ozero_ninf);
    check_uop(tan, czero_pinf);
    check_uop(tan, czero_ninf);

    cout << "=====================" << endl;
    check_uop(asin, i11);
    check_uop(asin, i12);
    check_uop(asin, i13);
    check_uop(asin, i14);
    check_uop(asin, i15);
    check_uop(asin, oi11);
    check_uop(asin, oi12);
    check_uop(asin, oi13);
    check_uop(asin, oi14);
    check_uop(asin, oi15);

    cout << "=====================" << endl;
    check_uop(acos, i11);
    check_uop(acos, i12);
    check_uop(acos, i13);
    check_uop(acos, i14);
    check_uop(acos, i15);
    check_uop(acos, oi11);
    check_uop(acos, oi12);
    check_uop(acos, oi13);
    check_uop(acos, oi14);
    check_uop(acos, oi15);

    cout << "=====================" << endl;
    check_uop(atan, i1);
    check_uop(atan, i2);
    check_uop(atan, i3);
    check_uop(atan, i4);
    check_uop(atan, i5);
    check_uop(atan, i6);
    check_uop(atan, i7);
    check_uop(atan, i8);
    check_uop(atan, i9);
    check_uop(atan, i10);
    check_uop(atan, oi1);
    check_uop(atan, oi2);
    check_uop(atan, oi3);
    check_uop(atan, oi4);
    check_uop(atan, oi5);
    check_uop(atan, oi6);
    check_uop(atan, oi7);
    check_uop(atan, oi8);
    check_uop(atan, oi9);
    check_uop(atan, oi10);
    check_uop(atan, inf);
    check_uop(atan, ozero_pinf);
    check_uop(atan, ozero_ninf);
    check_uop(atan, czero_pinf);
    check_uop(atan, czero_ninf);

    cout << "=====================" << endl;
    check_uop(sinh, i1);
    check_uop(sinh, i2);
    check_uop(sinh, i3);
    check_uop(sinh, i4);
    check_uop(sinh, i5);
    check_uop(sinh, i6);
    check_uop(sinh, i7);
    check_uop(sinh, i8);
    check_uop(sinh, i9);
    check_uop(sinh, i10);
    check_uop(sinh, oi1);
    check_uop(sinh, oi2);
    check_uop(sinh, oi3);
    check_uop(sinh, oi4);
    check_uop(sinh, oi5);
    check_uop(sinh, oi6);
    check_uop(sinh, oi7);
    check_uop(sinh, oi8);
    check_uop(sinh, oi9);
    check_uop(sinh, oi10);
    check_uop(sinh, inf);
    check_uop(sinh, ozero_pinf);
    check_uop(sinh, ozero_ninf);
    check_uop(sinh, czero_pinf);
    check_uop(sinh, czero_ninf);

    cout << "=====================" << endl;
    check_uop(cosh, i1);
    check_uop(cosh, i2);
    check_uop(cosh, i3);
    check_uop(cosh, i4);
    check_uop(cosh, i5);
    check_uop(cosh, i6);
    check_uop(cosh, i7);
    check_uop(cosh, i8);
    check_uop(cosh, i9);
    check_uop(cosh, i10);
    check_uop(cosh, oi1);
    check_uop(cosh, oi2);
    check_uop(cosh, oi3);
    check_uop(cosh, oi4);
    check_uop(cosh, oi5);
    check_uop(cosh, oi6);
    check_uop(cosh, oi7);
    check_uop(cosh, oi8);
    check_uop(cosh, oi9);
    check_uop(cosh, oi10);
    check_uop(cosh, inf);
    check_uop(cosh, ozero_pinf);
    check_uop(cosh, ozero_ninf);
    check_uop(cosh, czero_pinf);
    check_uop(cosh, czero_ninf);

    cout << "=====================" << endl;
    check_uop(tanh, i1);
    check_uop(tanh, i2);
    check_uop(tanh, i3);
    check_uop(tanh, i4);
    check_uop(tanh, i5);
    check_uop(tanh, i6);
    check_uop(tanh, i7);
    check_uop(tanh, i8);
    check_uop(tanh, i9);
    check_uop(tanh, i10);
    check_uop(tanh, oi1);
    check_uop(tanh, oi2);
    check_uop(tanh, oi3);
    check_uop(tanh, oi4);
    check_uop(tanh, oi5);
    check_uop(tanh, oi6);
    check_uop(tanh, oi7);
    check_uop(tanh, oi8);
    check_uop(tanh, oi9);
    check_uop(tanh, oi10);
    check_uop(tanh, inf);
    check_uop(tanh, ozero_pinf);
    check_uop(tanh, ozero_ninf);
    check_uop(tanh, czero_pinf);
    check_uop(tanh, czero_ninf);
}

int main() {
    enable_trace("numerics");
    mpfp_interval_arith();
    mpfp_interval_inf1();
    mpfp_interval_inf2();
    mpfp_interval_trans();
    return has_violations() ? 1 : 0;
}
