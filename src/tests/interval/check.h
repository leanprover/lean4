/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <string>

using std::cout;
using std::endl;

using namespace lean;

template <typename T1, typename T2, typename F>
void check_interval_bop(std::string const & fname, std::string const & varname, interval<T1> i, T2 c, interval<T1> r, F f) {
    cout << fname << "(" << varname << " " << i << ", " << c << ") = ";
    cout << r << endl;
    if (!i.is_lower_inf()) {
        T1 ll = i.lower();
        T1 lu = i.lower();
        numeric_traits<T1>::set_rounding(false);
        f(ll, c);
        numeric_traits<T1>::set_rounding(true);
        f(lu, c);
        cout << "\t" << fname << "(" << i.lower() << ", " << c << ") = [" << ll << ", " << lu << "]"<< endl;
        lean_assert(r.is_lower_inf() || r.lower() <= ll, r, ll);
        lean_assert(r.is_lower_inf() || r.lower() <= lu, r, lu);
        lean_assert(r.is_upper_inf() || ll <= r.upper(), r, ll);
        lean_assert(r.is_upper_inf() || lu <= r.upper(), r, lu);
    }
    if (!i.is_upper_inf()) {
        T1 ul = i.upper();
        T1 uu = i.upper();
        numeric_traits<T1>::set_rounding(false);
        f(ul, c);
        numeric_traits<T1>::set_rounding(true);
        f(uu, c);
        cout << "\t" << fname << "(" << i.upper() << ", " << c << ") = [" << ul << ", " << uu << "]" << endl;
        lean_assert(r.is_lower_inf() || r.lower() <= ul, r, ul);
        lean_assert(r.is_lower_inf() || r.lower() <= uu, r, uu);
        lean_assert(r.is_upper_inf() || ul <= r.upper(), r, ul);
        lean_assert(r.is_upper_inf() || uu <= r.upper(), r, uu);
    }
}

template <typename T, typename F>
void check_interval_uop(std::string const & fname, std::string const & varname, interval<T> i, interval<T> r, F f) {
    cout.precision(30);
    cout << fname << "(" << varname << " " << i << ") = ";
    cout << r << endl;
    if (!i.is_lower_inf()) {
        T ll = i.lower();
        T lu = i.lower();
        numeric_traits<T>::set_rounding(false);
        f(ll);
        numeric_traits<T>::set_rounding(true);
        f(lu);
        cout << "\t" << fname << "(" << i.lower() << ") = [" << ll << ", " << lu << "]"<< endl;
        lean_assert(r.is_lower_inf() || r.lower() <= ll, r, ll);
        lean_assert(r.is_lower_inf() || r.lower() <= lu, r, lu);
        lean_assert(r.is_upper_inf() || ll <= r.upper(), r, ll);
        lean_assert(r.is_upper_inf() || lu <= r.upper(), r, lu);
    }
    if (!i.is_upper_inf()) {
        T ul = i.upper();
        T uu = i.upper();
        numeric_traits<T>::set_rounding(false);
        f(ul);
        numeric_traits<T>::set_rounding(true);
        f(uu);
        cout << "\t" << fname << "(" << i.upper() << ") = [" << ul << ", " << uu << "]" << endl;
        lean_assert(r.is_lower_inf() || r.lower() <= ul, r, ul);
        lean_assert(r.is_lower_inf() || r.lower() <= uu, r, uu);
        lean_assert(r.is_upper_inf() || ul <= r.upper(), r, ul);
        lean_assert(r.is_upper_inf() || uu <= r.upper(), r, uu);
    }
}

#define print_result(a, op, b, r) \
    cout << a << " " << op << " " << b << " = " << r << endl;

#define check_bop(T, f, i, c)                                   \
    check_interval_bop(#f, #i, i, c, f(i, c), numeric_traits<T>::f)

#define check_uop(T, f, i)                                      \
    check_interval_uop(#f, #i, i, f(i), numeric_traits<T>::f)
