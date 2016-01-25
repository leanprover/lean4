/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <unordered_map>
#include <string>
#include <algorithm>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/lp/column_info.h"
#include "util/lp/lp_primal_core_solver.h"
#include "util/lp/lp_solver.h"

namespace lean {
template <typename T, typename X>
class lp_primal_simplex: public lp_solver<T, X> {
    lp_primal_core_solver<T, X> * m_core_solver = nullptr;
    std::vector<X> m_low_bounds;
private:
    unsigned original_rows() { return this->m_external_rows_to_core_solver_rows.size(); }

    void fill_costs_and_x_for_first_stage_solver(unsigned original_number_of_columns);

    void init_buffer(unsigned k, std::vector<T> & r);

    void refactor();

    void set_scaled_costs();
public:
    lp_primal_simplex() {}

    column_info<T> * get_or_create_column_info(unsigned column);

    void set_status(lp_status status) {
        this->m_status = status;
    }

    lp_status get_status() {
        return this->m_status;
    }

    void fill_acceptable_values_for_x();


    void set_zero_bound(bool * bound_is_set, T * bounds,  unsigned i);

    void fill_costs_and_x_for_first_stage_solver_for_row(
                                                         int row,
                                                         unsigned & slack_var,
                                                         unsigned & artificial);



    std::string name_of_core_solver_column(unsigned j);


    void set_core_solver_bounds();

    void update_time_limit_from_starting_time(int start_time) {
        this->m_settings.time_limit -= (get_millisecond_span(start_time) / 1000.);
    }

    void find_maximal_solution();

    void fill_A_x_and_basis_for_stage_one_total_inf();

    void fill_A_x_and_basis_for_stage_one_total_inf_for_row(unsigned row);

    void solve_with_total_inf();


    ~lp_primal_simplex();

    bool bounds_hold(std::unordered_map<std::string, T> const & solution);

    T get_row_value(unsigned i, std::unordered_map<std::string, T> const & solution, bool print);

    bool row_constraint_holds(unsigned i, std::unordered_map<std::string, T> const & solution, bool print);

    bool row_constraints_hold(std::unordered_map<std::string, T> const & solution);


    T * get_array_from_map(std::unordered_map<std::string, T> const & solution);

    bool solution_is_feasible(std::unordered_map<std::string, T> const & solution) {
        return bounds_hold(solution) && row_constraints_hold(solution);
    }

    virtual T get_column_value(unsigned column) const {
        return this->get_column_value_with_core_solver(column, m_core_solver);
    }

    T get_current_cost() const;
};
}
