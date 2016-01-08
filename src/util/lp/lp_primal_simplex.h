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

    void fill_costs_and_x_for_first_stage_solver(unsigned original_number_of_columns) {
        unsigned slack_var = original_number_of_columns;
        unsigned artificial = original_number_of_columns + this->m_slacks;

        for (unsigned row = 0; row < this->row_count(); row++) {
            fill_costs_and_x_for_first_stage_solver_for_row(row, slack_var, artificial);
        }
    }

    void init_buffer(unsigned k, std::vector<T> & r) {
        for (unsigned i = 0; i < k; i++) {
            r[i] = 0;
        }
        r[k] = 1;
        for (unsigned i = this->row_count() -1; i > k; i--) {
            r[i] = 0;
        }
    }

    void refactor() {
        m_core_solver->init_lu();
        if (m_core_solver->factorization()->get_status() != LU_status::OK) {
            throw exception("cannot refactor");
        }
    }

    void set_scaled_costs() {
        unsigned j = this->number_of_core_structurals();
        while (j-- > 0) {
            this->set_scaled_cost(j);
        }
    }

    void stage_two() {
        std::cout << "starting stage 2" << std::endl;
        lean_assert(!m_core_solver->A_mult_x_is_off());
        int j = this->m_A->column_count() - 1;
        unsigned core_solver_cols = this->number_of_core_structurals();

        while (j >= core_solver_cols) {
            this->m_costs[j--] = numeric_traits<T>::zero();
        }

        set_scaled_costs();
        m_core_solver->set_status(lp_status::FEASIBLE);
        this->m_second_stage_iterations = m_core_solver->solve();
        this->m_status = m_core_solver->get_status();
        //     std::cout << "status is " << lp_status_to_string(this->m_status) << std::endl;
    }
public:
    lp_primal_simplex() {}



    column_info<T> * get_or_create_column_info(unsigned column) {
        auto it = this->m_columns.find(column);
        return (it == this->m_columns.end())? ( this->m_columns[column] = new column_info<T>) : it->second;
    }

    void set_status(lp_status status) {
        this->m_status = status;
    }

    lp_status get_status() {
        return this->m_status;
    }

    void fill_acceptable_values_for_x() {
        for (auto t : this->m_core_solver_columns_to_external_columns) {
            this->m_x[t.first] = numeric_traits<T>::zero();
            lean_assert(this->m_x[t.first] >= 0);
        }
    }


    void set_zero_bound(bool * bound_is_set, T * bounds,  unsigned i) {
        bound_is_set[i] = true;
        bounds[i] = numeric_traits<T>::zero();
    }

    void fill_costs_and_x_for_first_stage_solver_for_row(
                                                         int row,
                                                         unsigned & slack_var,
                                                         unsigned & artificial) {
        lean_assert(row >= 0 && row < this->row_count());
        auto & constraint = this->m_constraints[this->m_core_solver_rows_to_external_rows[row]];
        // we need to bring the program to the form Ax = b
        T rs = this->m_b[row];
        T artificial_cost =  - numeric_traits<T>::one();
        switch (constraint.m_relation) {
        case Equal: // no slack variable here
            this->m_column_types[artificial] = low_bound;
            this->m_costs[artificial] = artificial_cost; // we are maximizing, so the artificial, which is non-negatiive, will be pushed to zero
            this->m_basis[row] = artificial;
            if (rs >= 0) {
                (*this->m_A)(row, artificial) = numeric_traits<T>::one();
                this->m_x[artificial] = rs;
            } else {
                (*this->m_A)(row, artificial) = - numeric_traits<T>::one();
                this->m_x[artificial] = - rs;
            }
            artificial++;
            break;

        case Greater_or_equal:
            this->m_column_types[slack_var] = low_bound;
            (*this->m_A)(row, slack_var) = - numeric_traits<T>::one();

            if (rs > 0) {
                lean_assert(numeric_traits<T>::is_zero(this->m_x[slack_var]));
                // adding one artificial
                this->m_column_types[artificial] = low_bound;
                (*this->m_A)(row, artificial) = numeric_traits<T>::one();
                this->m_costs[artificial] = artificial_cost;
                this->m_basis[row] = artificial;
                this->m_x[artificial] = rs;
                artificial++;
            } else {
                // we can put a slack_var into the basis, and avoid adding an artificial variable
                this->m_basis[row] = slack_var;
                this->m_x[slack_var] = - rs;
            }
            slack_var++;
            break;
        case Less_or_equal:
            // introduce a non-negative slack variable
            this->m_column_types[slack_var] = low_bound;
            (*this->m_A)(row, slack_var) = numeric_traits<T>::one();

            if (rs < 0) {
                // adding one artificial
                lean_assert(numeric_traits<T>::is_zero(this->m_x[slack_var]));
                this->m_column_types[artificial] = low_bound;
                (*this->m_A)(row, artificial) = - numeric_traits<T>::one();
                this->m_costs[artificial] = artificial_cost;
                this->m_x[artificial] = - rs;
                this->m_basis[row] = artificial++;
            } else {
                // we can put slack_var into the basis, and avoid adding an artificial variable
                this->m_basis[row] = slack_var;
                this->m_x[slack_var] = rs;
            }
            slack_var++;
            break;
        }
    }



    std::string name_of_core_solver_column(unsigned j) { // j here is the core solver index
        unsigned external_j = this->m_core_solver_columns_to_external_columns[j];
        auto t = this->m_columns.find(external_j);
        if (t == this->m_columns.end()) {
            return std::string("name_not_found");
        }
        return t->m_name;
    }


    void set_core_solver_bounds() {
        unsigned total_vars = this->m_A->column_count() + this->m_slacks + this->m_artificials;
        this->m_column_types.resize(total_vars);
        this->m_upper_bounds.resize(total_vars);
        for (auto cit : this->m_columns) {
            column_info<T> * ci = cit.second;
            auto p = this->m_external_columns_to_core_solver_columns.find(cit.first);
            if (p == this->m_external_columns_to_core_solver_columns.end()) continue;
            unsigned j = p->second;
            switch (this->m_column_types[j] = ci->get_column_type()){
            case fixed:
                this->m_upper_bounds[j] = numeric_traits<T>::zero();
                break;
            case boxed:
                this->m_upper_bounds[j] = ci->get_adjusted_upper_bound() / this->m_column_scale[j];
                break;

            default: break; // do nothing
            }
        }
    }

    void update_time_limit_from_starting_time(int start_time) {
        this->m_settings.time_limit -= (get_millisecond_span(start_time) / 1000.);
    }

    void find_maximal_solution() {
        int preprocessing_start_time = get_millisecond_count();
        if (this->problem_is_empty()) {
            this->m_status = lp_status::EMPTY;
            return;
        }

        this->cleanup();
        this->fill_matrix_A_and_init_right_side();
        if (this->m_status == lp_status::INFEASIBLE) {
            return;
        }
        this->m_x.resize(this->m_A->column_count());
        this->fill_m_b();
        this->scale();
        fill_acceptable_values_for_x();
        this->count_slacks_and_artificials();
        set_core_solver_bounds();
        update_time_limit_from_starting_time(preprocessing_start_time);
        solve_with_total_inf();
    }

    void fill_A_x_and_basis_for_stage_on_total_inf() {
        for (unsigned row = 0; row < this->row_count(); row++)
            fill_A_x_and_basis_for_stage_on_total_inf_for_row(row);
    }

    void fill_A_x_and_basis_for_stage_on_total_inf_for_row(unsigned row) {
        lean_assert(row < this->row_count());
        auto ext_row_it = this->m_core_solver_rows_to_external_rows.find(row);
        lean_assert(ext_row_it != this->m_core_solver_rows_to_external_rows.end());
        unsigned ext_row = ext_row_it->second;
        auto constr_it = this->m_constraints.find(ext_row);
        lean_assert(constr_it != this->m_constraints.end());
        auto & constraint = constr_it->second;
        unsigned j = this->m_A->column_count(); // j is a slack variable
        this->m_A->add_column();
        // we need to bring the program to the form Ax = b
        this->m_basis[row] = j;
        switch (constraint.m_relation) {
        case Equal:
            this->m_x[j] = this->m_b[row];
            (*this->m_A)(row, j) = numeric_traits<T>::one();
            this->m_column_types[j] = fixed;
            this->m_upper_bounds[j] = m_low_bounds[j] = zero_of_type<X>();
            break;

        case Greater_or_equal:
            this->m_x[j] = - this->m_b[row];
            (*this->m_A)(row, j) = - numeric_traits<T>::one();
            this->m_column_types[j] = low_bound;
            this->m_upper_bounds[j] = zero_of_type<X>();
            break;
        case Less_or_equal:
            this->m_x[j] = this->m_b[row];
            (*this->m_A)(row, j) = numeric_traits<T>::one();
            this->m_column_types[j] = low_bound;
            this->m_upper_bounds[j] = m_low_bounds[j] = zero_of_type<X>();
            break;
        }
    }

    void solve_with_total_inf() {
        std::cout << "starting solve_with_total_inf()" << std::endl;
        int total_vars = this->m_A->column_count() + this->row_count();
        m_low_bounds.clear();
        m_low_bounds.resize(total_vars, zero_of_type<X>());  // low bounds are shifted ot zero
        this->m_x.resize(total_vars, numeric_traits<T>::zero());
        this->m_basis.resize(this->row_count());
        this->m_costs.clear();
        this->m_costs.resize(total_vars, zero_of_type<T>());
        fill_A_x_and_basis_for_stage_on_total_inf();
        this->print_statistics_on_A();
        this->fill_column_names_for_core_solver();
        int j = this->m_A->column_count() - 1;
        unsigned core_solver_cols = this->number_of_core_structurals();

        while (j >= core_solver_cols)
            this->m_costs[j--] = numeric_traits<T>::zero();

        set_scaled_costs();
        m_core_solver = new lp_primal_core_solver<T, X>(*this->m_A,
                                                        this->m_b,
                                                        this->m_x,
                                                        this->m_basis,
                                                        this->m_costs,
                                                        this->m_column_types,
                                                        m_low_bounds,
                                                        this->m_upper_bounds,
                                                        this->m_settings, this->m_name_map);
        m_core_solver->solve();
        this->m_status = m_core_solver->m_status;
        this->m_total_iterations = m_core_solver->m_total_iterations;
     }


    // void stage_one_of_total_inf() {
    //     std::cout << "starting stage_one_of_total_inf()" << std::endl;
    //     int total_vars = this->m_A->column_count() + this->row_count();
    //     m_low_bounds.clear();
    //     m_low_bounds.resize(total_vars, zero_of_type<X>());  // low bounds are shifted ot zero
    //     this->m_x.resize(total_vars, numeric_traits<T>::zero());
    //     this->m_basis.resize(this->row_count());
    //     this->m_costs.clear();
    //     this->m_costs.resize(total_vars, zero_of_type<T>());
    //     fill_A_x_and_basis_for_stage_on_total_inf();
    //     this->print_statistics_on_A();
    //     this->fill_column_names_for_core_solver();
    //     m_core_solver = new lp_primal_core_solver<T, X>(*this->m_A,
    //                                                     this->m_b,
    //                                                     this->m_x,
    //                                                     this->m_basis,
    //                                                     this->m_costs,
    //                                                     this->m_column_types,
    //                                                     m_low_bounds,
    //                                                     this->m_upper_bounds,
    //                                                     this->m_settings, this->m_name_map);
    //     m_core_solver->find_feasible_solution();
    //     this->m_first_stage_iterations = m_core_solver->m_total_iterations;
    //     this->m_status = m_core_solver->m_status == lp_status::OPTIMAL? lp_status::FEASIBLE: m_core_solver->m_status; // just map FEASIBLE to OPTIMAL and do not change the rest
    // }

    ~lp_primal_simplex() {
        if (m_core_solver != nullptr) {
            delete m_core_solver;
         }
    }

    bool bounds_hold(std::unordered_map<std::string, T> const & solution) {
        for (auto it : this->m_columns) {
            auto sol_it = solution.find(it.second->get_name());
            if (sol_it == solution.end()) {
                std::cout << "cannot find column " << it.first << " in solution " << std::endl;
                throw;
            }

            if (!it.second->bounds_hold(sol_it->second)) {
                std::cout << "bounds do not hold for " << it.second->get_name() << std::endl;
                it.second->bounds_hold(sol_it->second);
                return false;
            }
        }
        return true;
    }

    T get_row_value(unsigned i, std::unordered_map<std::string, T> const & solution, bool print) {
        auto it = this->m_A_values.find(i);
        if (it == this->m_A_values.end()) {
            std::cout << "cannot find row " << i << std::endl;
            throw "get_row_value";
        }
        T ret = numeric_traits<T>::zero();
        for (auto & pair : it->second) {
            auto cit = this->m_columns.find(pair.first);
            if (cit == this->m_columns.end()){
                std::cout << "cannot find column " << pair.first << std::endl;
            }

            column_info<T> * ci = cit->second;
            auto sol_it = solution.find(ci->get_name());
            if (sol_it == solution.end()) {
                std::cout << "cannot find in the solution column " << ci->get_name() << std::endl;
            }
            T column_val = sol_it->second;
            if (print) {
                std::cout << pair.second << "(" << ci->get_name() << "=" << column_val << ") ";
            }
            ret += pair.second * column_val;
        }
        if (print) {
            std::cout << " = " << ret << std::endl;
        }
        return ret;
    }

    bool row_constraint_holds(unsigned i, std::unordered_map<std::string, T> const & solution, bool print) {
        T row_val = get_row_value(i, solution, print);
        auto & constraint = this->m_constraints[i];
        T rs = constraint.m_rs;
        switch (constraint.m_relation) {
        case Equal:
            if (fabs(numeric_traits<T>::get_double(row_val - rs)) > 0.00001) {
                if (print) {
                    std::cout << "should be = " << rs << std::endl;
                }
                return false;
            }
            return true;
        case Greater_or_equal:
            if (numeric_traits<T>::get_double(row_val - rs) < -0.00001) {
                if (print) {
                    std::cout << "should be >= " << rs << std::endl;
                }
                return false;
            }
            return true;;

        case Less_or_equal:
            if (numeric_traits<T>::get_double(row_val - rs) > 0.00001) {
                if (print) {
                    std::cout << "should be <= " << rs << std::endl;
                }
                return false;
            }
            return true;;
        }
        std::cout << "throw in row_constraint_holds " << std::endl;
        throw "wrong case";
    }

    bool row_constraints_hold(std::unordered_map<std::string, T> const & solution) {
        for (auto it : this->m_A_values) {
            if (!row_constraint_holds(it.first, solution, false)) {
                row_constraint_holds(it.first, solution, true);
                return false;
            }
        }
        return true;
    }


    T * get_array_from_map(std::unordered_map<std::string, T> const & solution) {
        T * t = new T[solution.size()];
        for (auto it : solution) {
            auto g = this->m_names_to_columns.find(it.first);
            if (g == this->m_names_to_columns.end()) {
                throw exception(sstream() << "cannot find name " << it.first);
            }
            t[g->second] = it.second;
        }
        return t;
    }

    bool solution_is_feasible(std::unordered_map<std::string, T> const & solution) {
        return bounds_hold(solution) && row_constraints_hold(solution);
    }

    virtual T get_column_value(unsigned column) const {
        return this->get_column_value_with_core_solver(column, m_core_solver);
    }

    T get_current_cost() const {
        T ret = numeric_traits<T>::zero();
        for (auto it : this->m_columns) {
            ret += this->get_column_cost_value(it.first, it.second);
        }
        return ret;
    }
};
}
