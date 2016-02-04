/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <string>
#include <algorithm>
#include <limits>
#include <sys/timeb.h>
#include "util/debug.h"
#include "util/numerics/numeric_traits.h"
#include "util/sstream.h"
#include "util/numerics/mpq.h"

namespace lean {

enum column_type  {
    fixed,
    boxed,
    low_bound,
    upper_bound,
    free_column
};

std::string column_type_to_string(column_type t);

enum lp_status {
    UNKNOWN,
    INFEASIBLE,
    TENTATIVE_UNBOUNDED,
    UNBOUNDED,
    TENTATIVE_DUAL_UNBOUNDED,
    DUAL_UNBOUNDED,
    OPTIMAL,
    FEASIBLE,
    FLOATING_POINT_ERROR,
    TIME_EXHAUSTED,
    ITERATIONS_EXHAUSTED,
    EMPTY,
    UNSTABLE
};

const char* lp_status_to_string(lp_status status);

lp_status lp_status_from_string(std::string status);

enum non_basic_column_value_position { at_low_bound, at_upper_bound, at_fixed, free_of_bounds };

template <typename X> bool is_epsilon_small(const X & v, const double& eps);    // forward definition
template <typename X> bool precise() { return numeric_traits<X>::precise();}
template <typename X> X zero_of_type() { return numeric_traits<X>::zero(); }
template <typename X> X one_of_type() { return numeric_traits<X>::one(); }
template <typename X> bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
template <typename X> double  get_double(const X & v) { return numeric_traits<X>::get_double(v); }

struct lp_settings {
    // when the absolute value of an element is less than pivot_epsilon
    // in pivoting, we treat it as a zero
    double pivot_epsilon = 0.00000001;
    // see Chatal, page 115
    double positive_price_epsilon = 1e-7;
    // a quatation "if some choice of the entering vairable leads to an eta matrix
    // whose diagonal element in the eta column is less than e2 (entering_diag_epsilon) in magnitude, the this choice is rejected ...
    double entering_diag_epsilon = 1e-8;
    double c_partial_pivoting = 10; // this is the constant c from page 410
    unsigned depth_of_rook_search = 4;
    bool using_partial_pivoting = true;
    // dissertation of Achim Koberstein
    // if Bx - b is different at any component more that refactor_epsilon then we refactor
    double refactor_tolerance = 1e-4;
    double pivot_tolerance = 1e-6;
    double zero_tolerance = 1e-12;
    double drop_tolerance = 1e-14;
    double tolerance_for_artificials = 1e-4;
    double can_be_taken_to_basis_tolerance = 0.00001;

    unsigned percent_of_entering_to_check = 5; // we try to find a profitable column in a percentage of the columns
    bool use_scaling = true;
    double scaling_maximum = 1;
    double scaling_minimum = 0.5;
    double harris_feasibility_tolerance = 1e-7; // page 179 of Istvan Maros
    double ignore_epsilon_of_harris = 10e-5;
    unsigned max_number_of_iterations_with_no_improvements = 2000000;
    unsigned max_total_number_of_iterations = 20000000;
    double time_limit = std::numeric_limits<double>::max(); // the maximum time limit of the total run time in seconds
    // dual section
    double dual_feasibility_tolerance = 1e-7; // // page 71 of the PhD thesis of Achim Koberstein
    double primal_feasibility_tolerance = 1e-7; // page 71 of the PhD thesis of Achim Koberstein
    double relative_primal_feasibility_tolerance = 1e-9; // page 71 of the PhD thesis of Achim Koberstein


    template <typename T> static bool is_eps_small_general(const T & t, const double & eps) {
        return (!numeric_traits<T>::precise())? is_epsilon_small<T>(t, eps) : numeric_traits<T>::is_zero(t);
    }

    template <typename T>
    bool abs_val_is_smaller_than_dual_feasibility_tolerance(T const & t) {
        return is_eps_small_general<T>(t, dual_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_primal_feasibility_tolerance(T const & t) {
        return is_eps_small_general<T>(t, dual_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_can_be_taken_to_basis_tolerance(T const & t) {
        return is_eps_small_general<T>(t, can_be_taken_to_basis_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_drop_tolerance(T const & t) {
        return is_eps_small_general<T>(t, drop_tolerance);
    }


    template <typename T>
    bool abs_val_is_smaller_than_zero_tolerance(T const & t) {
        return is_eps_small_general<T>(t, zero_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_refactor_tolerance(T const & t) {
        return is_eps_small_general<T>(t, refactor_tolerance);
    }


    template <typename T>
    bool abs_val_is_smaller_than_pivot_tolerance(T const & t) {
        return is_eps_small_general<T>(t, pivot_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_harris_tolerance(T const & t) {
        return is_eps_small_general<T>(t, harris_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_ignore_epslilon_for_harris(T const & t) {
        return is_eps_small_general<T>(t, ignore_epsilon_of_harris);
    }

    template <typename T>
    bool abs_val_is_smaller_than_artificial_tolerance(T const & t) {
        return is_eps_small_general<T>(t, tolerance_for_artificials);
    }
    // the method of lar solver to use
    bool row_feasibility = true;
    bool use_double_solver_for_lar = true;
    int report_frequency = 10000000;
    unsigned column_norms_update_frequency = 1000;
    bool scale_with_ratio = true;
    double density_threshold = 0.7; // need to tune it up, todo
#ifdef LEAN_DEBUG
    bool dense_deb;
    static unsigned ddd; // used for debugging
#endif
}; // end of lp_settings class

int get_millisecond_count();
int get_millisecond_span(int start_time);
void my_random_init(unsigned * seed);
unsigned my_random();

template <typename T>
std::string T_to_string(const T & t) {
    std::ostringstream strs;
    strs << t;
    return strs.str();
}

inline std::string T_to_string(const mpq & t) {
    std::ostringstream strs;
    strs << t.get_double();
    return strs.str();
}

template <typename T>
bool val_is_smaller_than_eps(T const & t, double const & eps) {
    if (!numeric_traits<T>::precise()) {
        return numeric_traits<T>::get_double(t) < eps;
    }
    return t <= numeric_traits<T>::zero();
}

template <typename T>
bool vectors_are_equal(T * a, std::vector<T>  &b, unsigned n);

template <typename T>
bool vectors_are_equal(const std::vector<T> & a, const buffer<T>  &b);

template <typename T>
bool vectors_are_equal(const std::vector<T> & a, const std::vector<T> &b);

template <typename T>
T abs (T const & v) { return v >= zero_of_type<T>() ? v : -v; }

template <typename X>
X max_abs_in_vector(std::vector<X>& t){
    X r(zero_of_type<X>());
    for (auto & v : t)
        r = std::max(abs(v) , r);
    return r;
}
inline void print_blanks(int n, std::ostream & out) {
    while (n--) {out << ' '; }
}
}

