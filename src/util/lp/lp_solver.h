/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <string>
#include <unordered_map>
#include <algorithm>
#include <vector>
#include "util/exception.h"
#include "util/sstream.h"
#include "util/lp/lp_settings.h"
#include "util/lp/column_info.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lp_core_solver_base.h"
#include "util/lp/scaler.h"
namespace lean {
enum lp_relation  {
    Less_or_equal,
    Equal,
    Greater_or_equal
};

template <typename T, typename X>
struct lp_constraint {
    X m_rs; // right side of the constraint
    lp_relation m_relation;
    lp_constraint() {} // empty constructor
    lp_constraint(T rs, lp_relation relation): m_rs(rs), m_relation(relation) {}
};

template <typename T, typename X>
class lp_solver {
    column_info<T> * get_or_create_column_info(unsigned column) {
        auto it = m_columns.find(column);
        return (it == m_columns.end())? ( m_columns[column] = new column_info<T>) : it->second;
    }

protected:
    T get_column_cost_value(unsigned j, column_info<T> * ci) const {
        if (ci->is_fixed()) {
            return ci->get_cost() * ci->get_fixed_value();
        }
        return ci->get_cost() * get_column_value(j);
    }
public:
    unsigned m_total_iterations;
    static_matrix<T, X>* m_A = nullptr; // this is the matrix of constraints
    std::vector<T> m_b; // the right side vector
    unsigned m_first_stage_iterations = 0;
    unsigned m_second_stage_iterations = 0;
    std::unordered_map<unsigned, lp_constraint<T, X>> m_constraints;
    std::unordered_map<unsigned, column_info<T>*> m_columns;
    std::unordered_map<unsigned, std::unordered_map<unsigned, T> > m_A_values;
    std::unordered_map<std::string, unsigned> m_names_to_columns; // don't have to use it
    std::unordered_map<unsigned, unsigned> m_external_rows_to_core_solver_rows;
    std::unordered_map<unsigned, unsigned> m_core_solver_rows_to_external_rows;
    std::unordered_map<unsigned, unsigned> m_external_columns_to_core_solver_columns;
    std::unordered_map<unsigned, unsigned> m_core_solver_columns_to_external_columns;
    std::vector<T> m_column_scale;
    std::unordered_map<unsigned, std::string>  m_name_map;
    unsigned m_artificials = 0;
    unsigned m_slacks = 0;
    std::vector<column_type> m_column_types;
    std::vector<T> m_costs;
    std::vector<T> m_x;
    std::vector<T> m_upper_bounds;
    std::vector<unsigned> m_basis;

    lp_status m_status = lp_status::UNKNOWN;

    lp_settings m_settings;
    lp_solver() {}

    unsigned row_count() const { return this->m_A->row_count(); }

    void add_constraint(lp_relation relation, T  right_side, unsigned row_index) {
        lean_assert(m_constraints.find(row_index) == m_constraints.end());
        lp_constraint<T, X> cs(right_side, relation);
        m_constraints[row_index] = cs;
    }

    void set_cost_for_column(unsigned column, T  column_cost) {
        get_or_create_column_info(column)->set_cost(column_cost);
    }

    void set_row_column_coefficient(unsigned row, unsigned column, T const & val) {
        m_A_values[row][column] = val;
    }
    // returns the current cost
    virtual T get_current_cost() const = 0;
       // do not have to call it
    void give_symbolic_name_to_column(std::string name, unsigned column) {
        auto it = m_columns.find(column);
        column_info<T> *ci;
        if (it == m_columns.end()){
            m_columns[column] = ci = new column_info<T>;
        } else {
            ci = it->second;
        }
        ci->set_name(name);
        m_names_to_columns[name] = column;
    }

    virtual T get_column_value(unsigned column) const = 0;

    T get_column_value_by_name(std::string name) const {
        auto it = m_names_to_columns.find(name);
        if (it == m_names_to_columns.end()) {
            throw exception(sstream() << "get_column_value_by_name " << name);
        }
        return get_column_value(it -> second);
    }

    // returns -1 if not found
    virtual int get_column_index_by_name(std::string name) const {
        auto t = m_names_to_columns.find(name);
        if (t == m_names_to_columns.end()) {
            return -1;
        }
        return t->second;
    }

    void set_low_bound(unsigned i, T bound) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_low_bound(bound);
    }

    void set_upper_bound(unsigned i, T bound) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_upper_bound(bound);
    }

    void unset_low_bound(unsigned i) {
        get_or_create_column_info(i)->unset_low_bound();
    }

    void unset_upper_bound(unsigned i) {
        get_or_create_column_info(i)->unset_upper_bound();
    }

    void set_fixed_value(unsigned i, T val) {
        column_info<T> *ci = get_or_create_column_info(i);
        ci->set_fixed_value(val);
    }

    void unset_fixed_value(unsigned i) {
        get_or_create_column_info(i)->unset_fixed();
    }

    lp_status get_status() const {
        return m_status;
    }

    virtual ~lp_solver(){
        if (m_A != nullptr) {
            delete m_A;
        }
        for (auto t : m_columns) {
            delete t.second;
        }
    }

    void flip_costs() {
        for (auto t : m_columns) {
            column_info<T> *ci = t.second;
            ci->set_cost(-ci->get_cost());
        }
    }

    virtual void find_maximal_solution() = 0;
    void set_time_limit(unsigned time_limit_in_seconds) {
        m_settings.time_limit = time_limit_in_seconds;
    }

    void set_max_iterations_per_stage(unsigned max_iterations) {
        m_settings.max_total_number_of_iterations = max_iterations;
    }

    void get_max_iterations_per_stage() const {
        return m_settings.max_total_number_of_iterations;
    }
protected:
    bool problem_is_empty() {
        for (auto & c : m_A_values)
            if (c.second.size())
                return false;
        return true;
    }

      void scale() {
         if (numeric_traits<T>::precise() || m_settings.use_scaling == false) {
             m_column_scale.clear();
             m_column_scale.resize(m_A->column_count(), one_of_type<T>());
             return;
         }

         T smin = T(m_settings.scaling_minimum);
         T smax = T(m_settings.scaling_maximum);

         scaler<T, X> scaler(m_b, *m_A, smin, smax, m_column_scale, this->m_settings);
         if (!scaler.scale()) {
             unscale();
         }
    }


    void print_rows_scale_stats() {
        std::cout << "rows max" << std::endl;
        for (unsigned i = 0; i < m_A->row_count(); i++) {
            print_row_scale_stats(i);
        }
        std::cout << std::endl;
    }

    void print_columns_scale_stats() {
        std::cout << "columns max" << std::endl;
        for (unsigned i = 0; i < m_A->column_count(); i++) {
            print_column_scale_stats(i);
        }
        std::cout << std::endl;
    }

    void print_row_scale_stats(unsigned i) {
        std::cout << "(" << std::min(m_A->get_min_abs_in_row(i), abs(m_b[i])) << " ";
        std::cout << std::max(m_A->get_max_abs_in_row(i), abs(m_b[i])) << ")";
    }

    void print_column_scale_stats(unsigned j) {
        std::cout << "(" << m_A->get_min_abs_in_row(j) << " ";
        std::cout <<  m_A->get_max_abs_in_column(j) << ")";
    }

    void print_scale_stats() {
        print_rows_scale_stats();
        print_columns_scale_stats();
    }

    void get_max_abs_in_row(std::unordered_map<unsigned, T> & row_map) {
        T ret = numeric_traits<T>::zero();
        for (auto jp : row_map) {
            T ac = numeric_traits<T>::abs(jp->second);
            if (ac > ret) {
                ret = ac;
            }
        }
        return ret;
    }

    void pin_vars_down_on_row(std::unordered_map<unsigned, T> & row) {
        pin_vars_on_row_with_sign(row, - numeric_traits<T>::one());
    }

    void pin_vars_up_on_row(std::unordered_map<unsigned, T> & row) {
        pin_vars_on_row_with_sign(row, numeric_traits<T>::one());
    }

    void pin_vars_on_row_with_sign(std::unordered_map<unsigned, T> & row, T sign ) {
        std::unordered_map<unsigned, T> pinned;
        for (auto t : row) {
            unsigned j = t.first;
            column_info<T> * ci = m_columns[j];
            T a = t.second;
            if (a * sign > numeric_traits<T>::zero()) {
                lean_assert(ci->upper_bound_is_set());
                ci->set_fixed_value(ci->get_upper_bound());
            } else {
                lean_assert(ci->low_bound_is_set());
                ci->set_fixed_value(ci->get_low_bound());
            }
        }
    }

    bool get_minimal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound) {
        low_bound = numeric_traits<T>::zero();
        for (auto & t : row) {
            T a = t.second;
            column_info<T> * ci = m_columns[t.first];
            if (a > numeric_traits<T>::zero()) {
                if (ci->low_bound_is_set()) {
                    low_bound += ci->get_low_bound() * a;
                } else {
                    return false;
                }
            } else {
                if (ci->upper_bound_is_set()) {
                    low_bound += ci->get_upper_bound() * a;
                } else {
                    return false;
                }
            }
        }
        return true;
    }

    bool get_maximal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound) {
        low_bound = numeric_traits<T>::zero();
        for (auto & t : row) {
            T a = t.second;
            column_info<T> * ci = m_columns[t.first];
            if (a < numeric_traits<T>::zero()) {
                if (ci->low_bound_is_set()) {
                    low_bound += ci->get_low_bound() * a;
                } else {
                    return false;
                }
            } else {
                if (ci->upper_bound_is_set()) {
                    low_bound += ci->get_upper_bound() * a;
                } else {
                    return false;
                }
            }
        }
        return true;
    }

    bool row_is_zero(std::unordered_map<unsigned, T> & row) {
        for (auto & t : row) {
            if (!is_zero(t.second))
                return false;
        }
        return true;
    }

    bool row_e_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index) {
        T rs = m_constraints[row_index].m_rs;
        if (row_is_zero(row)) {
            if (!is_zero(rs))
                m_status = INFEASIBLE;
            return true;
        }

        T low_bound;
        bool lb = get_minimal_row_value(row, low_bound);
        if (lb) {
            T diff = low_bound - rs;
            if (!val_is_smaller_than_eps(diff, m_settings.refactor_tolerance)){
                // low_bound > rs + m_settings.refactor_epsilon
                m_status = INFEASIBLE;
                return true;
            }
            if (val_is_smaller_than_eps(-diff, m_settings.refactor_tolerance)){
                pin_vars_down_on_row(row);
                return true;
            }
        }

        T upper_bound;
        bool ub = get_maximal_row_value(row, upper_bound);
        if (ub) {
            T diff = rs - upper_bound;
            if (!val_is_smaller_than_eps(diff,  m_settings.refactor_tolerance)) {
                // upper_bound < rs - m_settings.refactor_tolerance
                m_status = INFEASIBLE;
                return true;
            }
            if (val_is_smaller_than_eps(-diff, m_settings.refactor_tolerance)){
                pin_vars_up_on_row(row);
                return true;
            }
        }

        return false;
    }

    int row_ge_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index) {
        T rs = m_constraints[row_index].m_rs;
        if (row_is_zero(row)) {
            if (rs > zero_of_type<X>())
                m_status = INFEASIBLE;
            return true;
        }

        T upper_bound;
        if (get_maximal_row_value(row, upper_bound)) {
            T diff = rs - upper_bound;
            if (!val_is_smaller_than_eps(diff, m_settings.refactor_tolerance)) {
                // upper_bound < rs - m_settings.refactor_tolerance
                m_status = INFEASIBLE;
                return true;
            }
            if (val_is_smaller_than_eps(-diff, m_settings.refactor_tolerance)){
                pin_vars_up_on_row(row);
                return true;
            }
        }

        return false;
    }

    bool row_le_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index) {
        T low_bound;
        T rs = m_constraints[row_index].m_rs;
        if (row_is_zero(row)) {
            if (rs < zero_of_type<X>())
                m_status = INFEASIBLE;
            return true;
        }

        if (get_minimal_row_value(row, low_bound)) {
            T diff = low_bound - rs;
            if (!val_is_smaller_than_eps(diff, m_settings.refactor_tolerance)){
                // low_bound > rs + m_settings.refactor_tolerance
                m_status = lp_status::INFEASIBLE;
                return true;
            }
            if (val_is_smaller_than_eps(-diff, m_settings.refactor_tolerance)){
                pin_vars_down_on_row(row);
                return true;
            }
        }

        return false;
    }

    // analyse possible max and min values that are derived from var boundaries
    // Let us say that the we have a "ge" constraint, and the min value is equal to the rs.
    // Then we know what values of the variables are. For each positive coeff of the row it has to be
    // the low boundary of the var and for a negative - the upper.

    // this routing also pins the variables to the boundaries
    bool row_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index ) {
        auto & constraint = m_constraints[row_index];
        switch (constraint.m_relation) {
        case lp_relation::Equal:
            return row_e_is_obsolete(row, row_index);

        case lp_relation::Greater_or_equal:
            return row_ge_is_obsolete(row, row_index);

        case lp_relation::Less_or_equal:
            return row_le_is_obsolete(row, row_index);
        }
        lean_unreachable();
    }

    void remove_fixed_or_zero_columns() {
        for (auto & i_row : m_A_values) {
            remove_fixed_or_zero_columns_from_row(i_row.first, i_row.second);
        }
    }

    void remove_fixed_or_zero_columns_from_row(unsigned i, std::unordered_map<unsigned, T> & row) {
        auto & constraint = m_constraints[i];
        std::vector<unsigned> removed;
        for (auto & col : row) {
            unsigned j = col.first;
            lean_assert(m_columns.find(j) != m_columns.end());
            column_info<T> * ci = m_columns[j];
            if (ci->is_fixed()) {
                removed.push_back(j);
                T aj = col.second;
                constraint.m_rs -= aj * ci->get_fixed_value();
            } else {
                if (numeric_traits<T>::is_zero(col.second)){
                    removed.push_back(j);
                }
            }
        }

        for (auto j : removed) {
            row.erase(j);
        }
    }

    unsigned try_to_remove_some_rows() {
        std::vector<unsigned> rows_to_delete;
        for (auto & t : m_A_values) {
            if (row_is_obsolete(t.second, t.first)) {
                rows_to_delete.push_back(t.first);
            }

            if (m_status == lp_status::INFEASIBLE) {
                return 0;
            }
        }
        if (rows_to_delete.size() > 0) {
            for (unsigned k : rows_to_delete) {
                m_A_values.erase(k);
            }
        }
        remove_fixed_or_zero_columns();
        return rows_to_delete.size();
    }

    void cleanup() {
        int n = 0; // number of deleted rows
        int d;
        while ((d = try_to_remove_some_rows()))
            n += d;

        if (n == 1)
            std::cout << "deleted one row" << std::endl;
        else if (n)
            std::cout << "deleted " << n << " rows" << std::endl;
    }

    void map_external_rows_to_core_solver_rows() {
        unsigned size = 0;
        for (auto & row : m_A_values) {
            m_external_rows_to_core_solver_rows[row.first] = size;
            m_core_solver_rows_to_external_rows[size] = row.first;
            size++;
        }
    }

    void map_external_columns_to_core_solver_columns() {
        unsigned size = 0;
        for (auto & row : m_A_values) {
            for (auto & col : row.second) {
                if (col.second == numeric_traits<T>::zero() || m_columns[col.first]->is_fixed()) {
                    throw exception("found fixed column");
                }
                unsigned j = col.first;
                auto j_place = m_external_columns_to_core_solver_columns.find(j);
                if (j_place == m_external_columns_to_core_solver_columns.end()) { // j is a newcomer
                    m_external_columns_to_core_solver_columns[j] = size;
                    m_core_solver_columns_to_external_columns[size++] = j;
                }
            }
        }
    }

    void fill_column_names_for_core_solver() {
        for (auto it : this->m_columns) {
            auto p = this->m_external_columns_to_core_solver_columns.find(it.first);
            if (p != this->m_external_columns_to_core_solver_columns.end()) {
                this->m_name_map[p->second] = it.second->get_name();
            }
        }
    }

    unsigned number_of_core_structurals() { return m_external_columns_to_core_solver_columns.size(); }


    void restore_column_scales_to_one() {
        for (unsigned i = 0; i < m_column_scale.size(); i++) m_column_scale[i] = numeric_traits<T>::one();
    }

    void unscale() {
        delete m_A;
        m_A = nullptr;
        fill_A_from_A_values();
        restore_column_scales_to_one();
        fill_m_b();
    }

    void fill_A_from_A_values() {
        m_A = new static_matrix<T, X>(m_A_values.size(), number_of_core_structurals());
        for (auto & t : m_A_values) {
            lean_assert(m_external_rows_to_core_solver_rows.find(t.first) != m_external_rows_to_core_solver_rows.end());
            unsigned row =  m_external_rows_to_core_solver_rows[t.first];
            for (auto k : t.second) {
                lean_assert(m_external_columns_to_core_solver_columns.find(k.first) != m_external_columns_to_core_solver_columns.end());
                unsigned col = m_external_columns_to_core_solver_columns[k.first];
                bool col_is_flipped = m_columns[k.first]->is_flipped();

                if (!col_is_flipped) {
                    (*m_A)(row, col) = k.second;
                } else {
                    (*m_A)(row, col) = - k.second;
                }
            }
        }
    }

    void fill_matrix_A_and_init_right_side() {
        map_external_rows_to_core_solver_rows();
        map_external_columns_to_core_solver_columns();
        lean_assert(m_A == nullptr);
        fill_A_from_A_values();
        m_b.resize(m_A->row_count());
    }

    void count_slacks_and_artificials() {
        for (int i = row_count() - 1; i >= 0; i--) {
            count_slacks_and_artificials_for_row(i);
        }
    }

    void count_slacks_and_artificials_for_row(unsigned i) {
        lean_assert(this->m_constraints.find(this->m_core_solver_rows_to_external_rows[i]) != this->m_constraints.end());
        auto & constraint = this->m_constraints[this->m_core_solver_rows_to_external_rows[i]];
        T rs;
        switch (constraint.m_relation) {
        case Equal:
            m_artificials++;
            break;
        case Greater_or_equal:
            m_slacks++;
            rs = this->m_b[i];
            if (rs > 0) {
                m_artificials++;
            }
            break;
        case Less_or_equal:
            m_slacks++;
            rs = this->m_b[i];
            if (rs < 0) {
                m_artificials++;
            }
            break;
        }
    }

    T low_bound_shift_for_row(unsigned i) {
        T ret = numeric_traits<T>::zero();

        auto row = this->m_A_values.find(i);
        if (row == this->m_A_values.end()) {
            throw exception("cannot find row");
        }
        for (auto col : row->second) {
            ret += col.second * this->m_columns[col.first]->get_shift();
        }
        return ret;
    }

    void fill_m_b() {
        for (int i = this->row_count() - 1; i >= 0; i--) {
            lean_assert(this->m_constraints.find(this->m_core_solver_rows_to_external_rows[i]) != this->m_constraints.end());
            unsigned external_i = this->m_core_solver_rows_to_external_rows[i];
            auto & constraint = this->m_constraints[external_i];
            this->m_b[i] = constraint.m_rs - low_bound_shift_for_row(external_i);
        }
    }

    T get_column_value_with_core_solver(unsigned column, lp_core_solver_base<T, X> * core_solver) const {
        auto cit = this->m_columns.find(column);
        if (cit == this->m_columns.end()) {
            return numeric_traits<T>::zero();
        }

        column_info<T> * ci = cit->second;

        if (ci->is_fixed()) {
            return ci->get_fixed_value();
        }

        auto t = this->m_external_columns_to_core_solver_columns.find(column);
        if (t != this->m_external_columns_to_core_solver_columns.end()){
            unsigned cj = t->second;
            T v = core_solver->get_var_value(cj) * this->m_column_scale[cj];
            if (ci->is_free()) {
                return v;
            }
            if (!ci->is_flipped()) {
                return v + ci->get_low_bound();
            }

            // the flipped case when there is only upper bound
            return -v + ci->get_upper_bound(); //
        }

        return numeric_traits<T>::zero(); // returns zero for out of boundary columns
    }
    void set_scaled_cost(unsigned j) {
        // grab original costs but modify it with the column scales
        lean_assert(j < this->m_column_scale.size());
        column_info<T> * ci = this->m_columns[this->m_core_solver_columns_to_external_columns[j]];
        T cost = ci->get_cost();
        if (ci->is_flipped()){
            cost *= -1;
        }
        lean_assert(ci->is_fixed() == false);
        this->m_costs[j] = cost * this->m_column_scale[j];
    }
    void print_statistics_on_A() {
        std::cout << "extended A[" << this->m_A->row_count() << "," << this->m_A->column_count() << "]" << std::endl;
        // for (unsigned i = 0; i < this->m_A->row_count(); i++) {
        //  if (this->m_A->number_of_non_zeroes_in_row(i) <= 2 ) {
        //      std::cout << "m_p[" << i << "] = " << this->m_A->number_of_non_zeroes_in_row(i) << std::endl;
        //  }
        // }
    }
public:
    lp_settings & settings() { return m_settings;}
};
}
