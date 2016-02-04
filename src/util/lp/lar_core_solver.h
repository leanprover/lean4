/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <string>
#include "util/lp/lp_core_solver_base.h"
#include <algorithm>
#include "util/lp/indexed_vector.h"
#include "util/lp/binary_heap_priority_queue.h"
#include "util/lp/breakpoint.h"
namespace lean {

template <typename T, typename X>
class lar_core_solver : public lp_core_solver_base<T, X> {
    // m_sign_of_entering is set to 1 if the entering variable needs
    // to grow and is set to -1  otherwise
    int m_sign_of_entering_delta;
    X m_infeasibility;
    std::vector<unsigned> m_tight_basic_columns;
    std::vector<breakpoint<X>> m_breakpoints;
    binary_heap_priority_queue<X> m_breakpoint_indices_queue;
    std::vector<pair<mpq, unsigned>> m_infeasible_row;
    int m_infeasible_row_sign = 0;
    // with a breakpoint at this delta
public:
    lar_core_solver(std::vector<X> & x, std::vector<column_type> & column_types,
                    std::vector<X> & low_bounds, std::vector<X> & upper_bounds,
                    std::vector<unsigned> & basis,
                    static_matrix<T, X> & A,
                    lp_settings & settings,
                    std::unordered_map<unsigned, std::string> & column_names,
                    std::vector<X> & right_side,
                    std::vector<T> & costs);

    int get_infeasible_row_sign() const { return m_infeasible_row_sign;   }

    const std::vector<pair<mpq, unsigned>> & get_infeasibility_info(int & inf_sign) const {
        inf_sign = m_infeasible_row_sign;
        return m_infeasible_row;
    }

    void init_costs();

    void init_cost_for_column(unsigned j);

    void init_local();

    // returns m_sign_of_alpha_r
    int column_is_out_of_bounds(unsigned j);

    bool can_enter_basis_mpq(unsigned j);


    void calculate_pivot_row(unsigned i);


    X get_deb_inf_column(unsigned j);

    X get_deb_inf();

    bool debug_profit_delta(unsigned j, const T & delta, std::ostream & out);

    bool debug_profit(unsigned j, std::ostream & out);

    int choose_column_entering_basis();

    void one_iteration();


    void decide_on_status_when_cannot_enter();
    template <typename L>
    bool same_sign_with_entering_delta(const L & a) {
        return (a > zero_of_type<L>() && m_sign_of_entering_delta > 0) || (a < zero_of_type<L>() && m_sign_of_entering_delta < 0);
    }

    // j is the basic column, x is the value at x[j]
    // d is the coefficient before m_entering in the row with j as the basis column
    void try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value);
    void add_breakpoint(unsigned j, X delta, breakpoint_type type);

    void try_add_breakpoint_in_row(unsigned i);

    std::string break_type_to_string(breakpoint_type type);

    void print_breakpoint(const breakpoint<X> * b, std::ostream & out);

    void print_bound_info_and_x(unsigned j, std::ostream & out);

    void clear_breakpoints();

    void fill_breakpoints_array(unsigned entering);

    void advance_on_entering(unsigned entering);

    void print_cost(std::ostream & out);

    void update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta);

    void advance_on_sorted_breakpoints(unsigned entering);

    void change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering);

    bool row_is_infeasible(unsigned row, int & inf_sign);

    bool row_is_evidence(unsigned row, int & inf_sign);

    bool find_evidence_row();


    bool done();

    void move_as_many_as_possible_fixed_columns_to_non_basis();

    bool non_basis_columns_are_set_correctly();

    void prefix();

    bool is_tiny() const { return this->m_m < 10 && this->m_n < 20; }

    bool is_empty() const { return this->m_m == 0 || this->m_n == 0; }

    void feasibility_loop();

    unsigned get_number_of_inf_rows() const;


    void row_feasibility_loop();

    int find_infeasible_row(int & inf_sign);

    int get_infeasibility_sign(unsigned j) const;


    template <typename L>
    int get_sign(const L & v) {
        return v > zero_of_type<L>() ? 1 : (v < zero_of_type<L>() ? -1 : 0);
    }

    bool improves_pivot_row_inf(unsigned j, int inf_sign);

    int choose_entering_column_for_row_inf_strategy(int inf_sign);

    void fill_evidence(unsigned row, int inf_sign);


    void update_delta_of_entering_and_leaving_candidates(X del, X & delta,
                                                         std::vector<unsigned> & leaving_candidates,
                                                         unsigned bj);

    void update_delta_of_entering(int delta_sign, unsigned row, X & delta,
                                  std::vector<unsigned> & leaving_candidates);

    unsigned find_leaving_for_inf_row_strategy(std::vector<unsigned> & leaving_candidates) {
        lean_assert(leaving_candidates.size());
        return leaving_candidates[my_random() % leaving_candidates.size()]; // more randomness
    }

    X find_initial_delta_and_its_sign(unsigned row, unsigned entering,
                                      int inf_sign, int & entering_delta_sign,
                                      std::vector<unsigned> & leaving_candidates);

    void advance_on_infeasible_row_and_entering(unsigned inf_row, unsigned entering, int inf_sign);

    void advance_on_infeasible_row(unsigned i, int inf_sign);

    void solve();

    bool low_bounds_are_set() const { return true; }

    void print_column_info(unsigned j, std::ostream & out);
};
}
