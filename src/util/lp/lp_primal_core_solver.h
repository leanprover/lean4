/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <list>
#include <limits>
#include <unordered_map>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <math.h>
#include <cstdlib>
#include <algorithm>
#include "util/numerics/double.h"
#include "util/lp/lu.h"
#include "util/lp/lp_solver.h"
#include "util/lp/static_matrix.h"
#include "util/lp/core_solver_pretty_printer.h"
#include "util/lp/lp_core_solver_base.h"
#include "util/lp/breakpoint.h"
#include "util/lp/binary_heap_priority_queue.h"
namespace lean {

// This core solver solves (Ax=b, low_bound_values \leq x \leq upper_bound_values, maximize costs*x )
// The right side b is given implicitly by x and the basis
template <typename T, typename X>
class lp_primal_core_solver:public lp_core_solver_base<T, X> {
public:
    // m_sign_of_entering is set to 1 if the entering variable needs
    // to grow and is set to -1  otherwise
    unsigned m_column_norm_update_counter;
    T m_enter_price_eps;
    X m_infeasibility = zero_of_type<X>();
    int m_sign_of_entering_delta;
    std::vector<breakpoint<X>> m_breakpoints;
    binary_heap_priority_queue<X> m_breakpoint_indices_queue;
    bool m_using_inf_costs = false;
    bool m_recalc_reduced_costs = false;
    std::set<unsigned> m_forbidden_enterings;
    std::vector<T> m_beta; // see Swietanowski working vector beta for column norms
    T m_epsilon_of_reduced_cost = T(1e-7);
    bool m_exit_on_feasible_solution = false;
    std::vector<T> m_costs_backup;
    bool m_current_x_is_feasible;
    T m_converted_harris_eps;
    //    T m_converted_harris_eps = convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance);
    std::list<unsigned> m_non_basis_list;
    void sort_non_basis();
    int choose_entering_column(unsigned number_of_benefitial_columns_to_go_over);

    int find_leaving_and_t_precisely(unsigned entering, X & t);

    static X positive_infinity() {
        return convert_struct<X, double>::convert(std::numeric_limits<unsigned>::max());
    }

    X get_harris_theta();

    void restore_harris_eps() { m_converted_harris_eps = convert_struct<T, double>::convert(this->m_settings.harris_feasibility_tolerance); }
    void zero_harris_eps() { m_converted_harris_eps = zero_of_type<T>(); }
    bool get_current_x_is_feasible() const { return m_current_x_is_feasible; }
    bool get_current_x_is_infeasible() const { return !m_current_x_is_feasible; }
    int find_leaving_on_harris_theta(X const & harris_theta, X & t);
    bool try_jump_to_another_bound_on_entering(unsigned entering, const X & theta, X & t);
    int find_leaving_and_t(unsigned entering, X & t);

    void limit_theta_on_basis_column_for_inf_case_m_neg_upper_bound(unsigned j, const T & m, X & theta) {
        lean_assert(m < 0 && this->m_column_type[j] == upper_bound);
        limit_inf_on_upper_bound_m_neg(m, this->m_x[j], this->m_upper_bound_values[j], theta);
    }


    void limit_theta_on_basis_column_for_inf_case_m_neg_low_bound(unsigned j, const T & m, X & theta) {
        lean_assert(m < 0 && this->m_column_type[j] == low_bound);
        limit_inf_on_bound_m_neg(m, this->m_x[j], this->m_low_bound_values[j], theta);
    }


    void limit_theta_on_basis_column_for_inf_case_m_pos_low_bound(unsigned j, const T & m, X & theta) {
        lean_assert(m > 0 && this->m_column_type[j] == low_bound);
        limit_inf_on_low_bound_m_pos(m, this->m_x[j], this->m_low_bound_values[j], theta);
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_upper_bound(unsigned j, const T & m, X & theta) {
        lean_assert(m > 0 && this->m_column_type[j] == upper_bound);
        limit_inf_on_bound_m_pos(m, this->m_x[j], this->m_upper_bound_values[j], theta);
    };

    X harris_eps_for_bound(const X & bound) const { return ( convert_struct<X, double>::convert(1) +  abs(bound)/10) * m_converted_harris_eps/3;
    }


    void get_bound_on_variable_and_update_leaving_precisely(unsigned j, int & leaving, T m, X & t, T & abs_of_d_of_leaving);

    bool column_is_free(unsigned j) { return this->m_column_type[j] == free; }

    bool column_has_upper_bound(unsigned j) {
        return ((unsigned)this->m_column_type[j]) < 2;
    }

    bool column_has_low_bound(unsigned j) { return this->m_column_type[j] != free_column; }

    std::vector<T> m_low_bound_values_dummy; // needed for the base class only

    X get_max_bound(std::vector<X> & b);

    // stage1 constructor
    lp_primal_core_solver(static_matrix<T, X> & A,
                          std::vector<X> & b, // the right side vector
                          std::vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                          std::vector<unsigned> & basis,
                          std::vector<T> & costs,
                          std::vector<column_type> & column_type_array,
                          std::vector<X> & low_bound_values,
                          std::vector<X> & upper_bound_values,
                          lp_settings & settings,
                          std::unordered_map<unsigned, std::string> const & column_names);  // constructor
    lp_primal_core_solver(static_matrix<T, X> & A,
                          std::vector<X> & b, // the right side vector
                          std::vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                          std::vector<unsigned> & basis,
                          std::vector<T> & costs,
                          std::vector<column_type> & column_type_array,
                          std::vector<X> & upper_bound_values,
                          lp_settings & settings,
                          std::unordered_map<unsigned, std::string> const & column_names);
    bool initial_x_is_correct();
#ifdef LEAN_DEBUG
    void check_Ax_equal_b();
    void check_the_bounds();
    void check_bound(unsigned i);
    void check_correctness();
#endif

    // from page 183 of Istvan Maros's book
    // the basis structures have not changed yet
    void update_reduced_costs_from_pivot_row(unsigned entering, unsigned leaving);

    // return 0 if the reduced cost at entering is close enough to the refreshed
    // 1 if it is way off, and 2 if it is unprofitable
    int refresh_reduced_cost_at_entering_and_check_that_it_is_off(unsigned entering);

    void normalize_costs_and_backup_costs();

    void init_run();

    void calc_working_vector_beta_for_column_norms();

    void advance_on_entering_and_leaving(int entering, int leaving, X & t);

    bool need_to_switch_costs() const {
        lean_assert(calc_current_x_is_feasible() == m_current_x_is_feasible);
        return get_current_x_is_feasible() == m_using_inf_costs;
    }


    void advance_on_entering(int entering);

    void push_forward_offset_in_non_basis(unsigned & offset_in_nb);

    unsigned get_number_of_non_basic_column_to_try_for_enter();

    void print_column_norms(std::ostream & out);

    void set_current_x_is_feasible() { m_current_x_is_feasible = calc_current_x_is_feasible(); }
    // returns the number of iterations
    unsigned solve();

    lu<T, X> * factorization() {return this->m_factorization;}

    void delete_factorization();

    // according to Swietanowski, " A new steepest edge approximation for the simplex method for linear programming"
    void init_column_norms();

    T calculate_column_norm_exactly(unsigned j);

    void update_or_init_column_norms(unsigned entering, unsigned leaving);

    // following Swietanowski - A new steepest ...
    void update_column_norms(unsigned entering, unsigned leaving);

    T calculate_norm_of_entering_exactly();

    // calling it stage1 is too cryptic
    void find_feasible_solution();

    bool is_tiny() const {return this->m_m < 10 && this->m_n < 20;}

    void calculate_infeasibility();

    void add_column_infeasibility(unsigned j);

    void one_iteration();

    void fill_breakpoints_array(unsigned entering);

    void try_add_breakpoint_in_row(unsigned i);

    void clear_breakpoints();

    void change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering);
    void advance_on_sorted_breakpoints(unsigned entering);

    void update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta);
    bool column_is_feasible(unsigned j) const;

    bool calc_current_x_is_feasible() const;

    void decide_on_status_when_cannot_find_entering() {
        lean_assert(!need_to_switch_costs());
        this->m_status = get_current_x_is_feasible()? OPTIMAL: INFEASIBLE;
    }

    void limit_theta_on_basis_column_for_feas_case_m_neg(unsigned j, const T & m, X & theta) {
        lean_assert(m < 0);
        lean_assert(this->m_column_type[j] == low_bound || this->m_column_type[j] == boxed);
        const X & eps = harris_eps_for_bound(this->m_low_bound_values[j]);
        if (this->above_bound(this->m_x[j], this->m_low_bound_values[j])) {
            theta = std::min((this->m_low_bound_values[j] -this->m_x[j] - eps) / m, theta);
            if (theta < zero_of_type<X>()) theta = zero_of_type<X>();
        }
    }

    void limit_theta_on_basis_column_for_feas_case_m_neg_no_check(unsigned j, const T & m, X & theta) {
        lean_assert(m < 0);
        //        lean_assert(this->m_column_type[j] == low_bound || this->m_column_type[j] == boxed);
        const X& eps = harris_eps_for_bound(this->m_low_bound_values[j]);
        theta = std::min((this->m_low_bound_values[j] - this->m_x[j] - eps) / m, theta);
        if (theta < zero_of_type<X>()) theta = zero_of_type<X>();
    }

    bool limit_inf_on_bound_m_neg(const T & m, const X & x, const X & bound, X & theta) {
        // x gets smaller
        lean_assert(m < 0);
        const X& eps = harris_eps_for_bound(bound);
        if (this->below_bound(x, bound)) return false;
        if (this->above_bound(x, bound)) {
            theta = std::min((bound - x - eps) / m, theta);
        } else {
            theta = zero_of_type<X>();
        }
        return true;
    }

    bool limit_inf_on_bound_m_pos(const T & m, const X & x, const X & bound, X & theta) {
        // x gets larger
        lean_assert(m > 0);
        const X& eps = harris_eps_for_bound(bound);
        if (this->above_bound(x, bound)) return false;
        if (this->below_bound(x, bound)) {
            theta = std::min((bound - x + eps) / m, theta);
        } else {
            theta = zero_of_type<X>();
        }
        return true;
    }

    void limit_inf_on_low_bound_m_pos(const T & m, const X & x, const X & bound, X & theta) {
        // x gets larger
        lean_assert(m > 0);
        const X& eps = harris_eps_for_bound(bound);
        if (this->below_bound(x, bound))
            theta = std::min((bound - x + eps) / m, theta);
    }

    void limit_inf_on_upper_bound_m_neg(const T & m, const X & x, const X & bound, X & theta) {
        // x gets smaller
        lean_assert(m < 0);
        const X& eps = harris_eps_for_bound(bound);
        if (this->above_bound(x, bound))
            theta = std::min((bound - x - eps) / m, theta);
    }

    void limit_theta_on_basis_column_for_inf_case_m_pos_boxed(unsigned j, const T & m, X & theta) {
        //        lean_assert(m > 0 && this->m_column_type[j] == boxed);
        const X & x = this->m_x[j];
        const X & lbound = this->m_low_bound_values[j];

        if (this->below_bound(x, lbound)) {
            const X& eps = harris_eps_for_bound(this->m_upper_bound_values[j]);
            theta = std::min((lbound - x + eps) / m, theta);
        } else {
            const X & ubound = this->m_upper_bound_values[j];
            if (this->below_bound(x, ubound)){
                const X& eps = harris_eps_for_bound(ubound);
                theta = std::min((ubound - x + eps) / m, theta);
            } else if (!this->above_bound(x, ubound)) {
                theta = zero_of_type<X>();
            }
        }
    }

    void limit_theta_on_basis_column_for_inf_case_m_neg_boxed(unsigned j, const T & m, X & theta) {
        //  lean_assert(m < 0 && this->m_column_type[j] == boxed);
        const X & x = this->m_x[j];
        const X & ubound = this->m_upper_bound_values[j];
        if (this->above_bound(x, ubound)) {
            const X& eps = harris_eps_for_bound(ubound);
            theta = std::min((ubound - x - eps) / m, theta);
        } else {
            const X & lbound = this->m_low_bound_values[j];
            if (this->above_bound(x, lbound)){
                const X& eps = harris_eps_for_bound(lbound);
                theta = std::min((lbound - x - eps) / m, theta);
            } else if (!this->below_bound(x, lbound)) {
                theta = zero_of_type<X>();
            }
        }
    }
    void limit_theta_on_basis_column_for_feas_case_m_pos(unsigned j, const T & m, X & theta) {
        lean_assert(m > 0);
        const T& eps = harris_eps_for_bound(this->m_upper_bound_values[j]);
        if (this->below_bound(this->m_x[j], this->m_upper_bound_values[j])) {
            theta = std::min((this->m_upper_bound_values[j] - this->m_x[j] + eps) / m, theta);
            if (theta < zero_of_type<X>()) theta = zero_of_type<X>();
        }
    }

    void limit_theta_on_basis_column_for_feas_case_m_pos_no_check(unsigned j, const T & m, X & theta) {
        lean_assert(m > 0);
        const X& eps = harris_eps_for_bound(this->m_upper_bound_values[j]);
        theta = std::min((this->m_upper_bound_values[j] - this->m_x[j] + eps) / m, theta);
        if (theta < zero_of_type<X>()) theta = zero_of_type<X>();
    }

    // j is a basic column or the entering, in any case x[j] has to stay feasible.
    // m is the multiplier. updating t in a way that holds the following
    // x[j] + t * m >=  - harris_feasibility_tolerance ( if m < 0 )
    // or
    // x[j] + t * m <= this->m_upper_bound_values[j] + harris_feasibility_tolerance ( if m > 0)
    void limit_theta_on_basis_column(unsigned j, T m, X & theta) {
        switch (this->m_column_type[j]) {
        case free_column: break;
        case upper_bound:
            if (get_current_x_is_feasible()) {
                if (m > 0)
                    limit_theta_on_basis_column_for_feas_case_m_pos_no_check(j, m, theta);
            } else { // inside of feasibility_loop
                if (m > 0)
                    limit_theta_on_basis_column_for_inf_case_m_pos_upper_bound(j, m, theta);
                else
                    limit_theta_on_basis_column_for_inf_case_m_neg_upper_bound(j, m, theta);
            }
            break;
        case low_bound:
            if (get_current_x_is_feasible()) {
                if (m < 0)
                    limit_theta_on_basis_column_for_feas_case_m_neg_no_check(j, m, theta);
            } else {
                if (m < 0)
                    limit_theta_on_basis_column_for_inf_case_m_neg_low_bound(j, m, theta);
                else
                    limit_theta_on_basis_column_for_inf_case_m_pos_low_bound(j, m, theta);
            }
            break;
        // case fixed:
        //     if (get_current_x_is_feasible()) {
        //         theta = zero_of_type<X>();
        //         break;
        //     }
        //     if (m < 0)
        //         limit_theta_on_basis_column_for_inf_case_m_neg_fixed(j, m, theta);
        //     else
        //         limit_theta_on_basis_column_for_inf_case_m_pos_fixed(j, m, theta);
        //     break;
        case fixed:
        case boxed:
            if (get_current_x_is_feasible()) {
                if (m > 0) {
                    limit_theta_on_basis_column_for_feas_case_m_pos_no_check(j, m, theta);
                } else {
                    limit_theta_on_basis_column_for_feas_case_m_neg_no_check(j, m, theta);
                }
            } else {
                if (m > 0) {
                    limit_theta_on_basis_column_for_inf_case_m_pos_boxed(j, m, theta);
                } else {
                    limit_theta_on_basis_column_for_inf_case_m_neg_boxed(j, m, theta);
                }
            }

            break;
        default:
            lean_unreachable();
        }
        if (theta < zero_of_type<X>())
            theta = zero_of_type<X>();
    }


    bool can_enter_basis(unsigned j);
    bool done();

    void init_infeasibility_costs();

    void print_column(unsigned j, std::ostream & out);

    void init_infeasibility_cost_for_column(unsigned j);

    void add_breakpoint(unsigned j, X delta, breakpoint_type type);

    // j is the basic column, x is the value at x[j]
    // d is the coefficient before m_entering in the row with j as the basis column
    void try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value);
    template <typename L>
    bool same_sign_with_entering_delta(const L & a) {
        return (a > zero_of_type<L>() && m_sign_of_entering_delta > 0) || (a < zero_of_type<L>() && m_sign_of_entering_delta < 0);
    }

    void init_costs_from_backup();

    void init_reduced_costs();

    bool low_bounds_are_set() const { return true; }
    friend core_solver_pretty_printer<T, X>;
};
}
