/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
#include <algorithm>
#include <vector>
#include "util/lp/lp_solver.h"
namespace lean {
template <typename T, typename X> column_info<T> * lp_solver<T, X>::get_or_create_column_info(unsigned column) {
    auto it = m_columns.find(column);
    return (it == m_columns.end())? ( m_columns[column] = new column_info<T>) : it->second;
}


template <typename T, typename X> T lp_solver<T, X>::get_column_cost_value(unsigned j, column_info<T> * ci) const {
    if (ci->is_fixed()) {
        return ci->get_cost() * ci->get_fixed_value();
    }
    return ci->get_cost() * get_column_value(j);
}
template <typename T, typename X> void lp_solver<T, X>::add_constraint(lp_relation relation, T  right_side, unsigned row_index) {
    lean_assert(m_constraints.find(row_index) == m_constraints.end());
    lp_constraint<T, X> cs(right_side, relation);
    m_constraints[row_index] = cs;
}

template <typename T, typename X> void lp_solver<T, X>::give_symbolic_name_to_column(std::string name, unsigned column) {
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


template <typename T, typename X>  T lp_solver<T, X>::get_column_value_by_name(std::string name) const {
    auto it = m_names_to_columns.find(name);
    if (it == m_names_to_columns.end()) {
        throw exception(sstream() << "get_column_value_by_name " << name);
    }
    return get_column_value(it -> second);
}

// returns -1 if not found
template <typename T, typename X> int lp_solver<T, X>::get_column_index_by_name(std::string name) const {
    auto t = m_names_to_columns.find(name);
    if (t == m_names_to_columns.end()) {
        return -1;
    }
    return t->second;
}


template <typename T, typename X>  lp_solver<T, X>::~lp_solver(){
    if (m_A != nullptr) {
        delete m_A;
    }
    for (auto t : m_columns) {
        delete t.second;
    }
}

template <typename T, typename X> void lp_solver<T, X>::flip_costs() {
    for (auto t : m_columns) {
        column_info<T> *ci = t.second;
        ci->set_cost(-ci->get_cost());
    }
}

template <typename T, typename X>    bool lp_solver<T, X>::problem_is_empty() {
    for (auto & c : m_A_values)
        if (c.second.size())
            return false;
    return true;
}

template <typename T, typename X> void lp_solver<T, X>::scale() {
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


template <typename T, typename X> void lp_solver<T, X>::print_rows_scale_stats(std::ostream & out) {
    out << "rows max" << std::endl;
    for (unsigned i = 0; i < m_A->row_count(); i++) {
        print_row_scale_stats(i, out);
    }
    out << std::endl;
}

template <typename T, typename X> void lp_solver<T, X>::print_columns_scale_stats(std::ostream & out) {
    out << "columns max" << std::endl;
    for (unsigned i = 0; i < m_A->column_count(); i++) {
        print_column_scale_stats(i, out);
    }
    out << std::endl;
}

template <typename T, typename X> void lp_solver<T, X>::print_row_scale_stats(unsigned i, std::ostream & out) {
    out << "(" << std::min(m_A->get_min_abs_in_row(i), abs(m_b[i])) << " ";
    out << std::max(m_A->get_max_abs_in_row(i), abs(m_b[i])) << ")";
}

template <typename T, typename X> void lp_solver<T, X>::print_column_scale_stats(unsigned j, std::ostream & out) {
    out << "(" << m_A->get_min_abs_in_row(j) << " ";
    out <<  m_A->get_max_abs_in_column(j) << ")";
}

template <typename T, typename X> void lp_solver<T, X>::print_scale_stats(std::ostream & out) {
    print_rows_scale_stats(out);
    print_columns_scale_stats(out);
}

template <typename T, typename X> void lp_solver<T, X>::get_max_abs_in_row(std::unordered_map<unsigned, T> & row_map) {
    T ret = numeric_traits<T>::zero();
    for (auto jp : row_map) {
        T ac = numeric_traits<T>::abs(jp->second);
        if (ac > ret) {
            ret = ac;
        }
    }
    return ret;
}

template <typename T, typename X> void lp_solver<T, X>::pin_vars_on_row_with_sign(std::unordered_map<unsigned, T> & row, T sign ) {
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

template <typename T, typename X>    bool lp_solver<T, X>::get_minimal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound) {
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

template <typename T, typename X>    bool lp_solver<T, X>::get_maximal_row_value(std::unordered_map<unsigned, T> & row, T & low_bound) {
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

template <typename T, typename X>    bool lp_solver<T, X>::row_is_zero(std::unordered_map<unsigned, T> & row) {
    for (auto & t : row) {
        if (!is_zero(t.second))
            return false;
    }
    return true;
}

template <typename T, typename X>    bool lp_solver<T, X>::row_e_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index) {
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

template <typename T, typename X>    int lp_solver<T, X>::row_ge_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index) {
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

template <typename T, typename X>    bool lp_solver<T, X>::row_le_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index) {
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
template <typename T, typename X>    bool lp_solver<T, X>::row_is_obsolete(std::unordered_map<unsigned, T> & row, unsigned row_index ) {
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

template <typename T, typename X> void lp_solver<T, X>::remove_fixed_or_zero_columns() {
    for (auto & i_row : m_A_values) {
        remove_fixed_or_zero_columns_from_row(i_row.first, i_row.second);
    }
}

template <typename T, typename X> void lp_solver<T, X>::remove_fixed_or_zero_columns_from_row(unsigned i, std::unordered_map<unsigned, T> & row) {
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

template <typename T, typename X>    unsigned lp_solver<T, X>::try_to_remove_some_rows() {
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

template <typename T, typename X> void lp_solver<T, X>::cleanup() {
    int n = 0; // number of deleted rows
    int d;
    while ((d = try_to_remove_some_rows()))
        n += d;

    // if (n == 1)
    //     std::cout << "deleted one row" << std::endl;
    // else if (n)
    //     std::cout << "deleted " << n << " rows" << std::endl;
}

template <typename T, typename X> void lp_solver<T, X>::map_external_rows_to_core_solver_rows() {
    unsigned size = 0;
    for (auto & row : m_A_values) {
        m_external_rows_to_core_solver_rows[row.first] = size;
        m_core_solver_rows_to_external_rows[size] = row.first;
        size++;
    }
}

template <typename T, typename X> void lp_solver<T, X>::map_external_columns_to_core_solver_columns() {
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

template <typename T, typename X> void lp_solver<T, X>::fill_column_names_for_core_solver() {
    for (auto it : this->m_columns) {
        auto p = this->m_external_columns_to_core_solver_columns.find(it.first);
        if (p != this->m_external_columns_to_core_solver_columns.end()) {
            this->m_name_map[p->second] = it.second->get_name();
        }
    }
}


template <typename T, typename X> void lp_solver<T, X>::unscale() {
    delete m_A;
    m_A = nullptr;
    fill_A_from_A_values();
    restore_column_scales_to_one();
    fill_m_b();
}

template <typename T, typename X> void lp_solver<T, X>::fill_A_from_A_values() {
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

template <typename T, typename X> void lp_solver<T, X>::fill_matrix_A_and_init_right_side() {
    map_external_rows_to_core_solver_rows();
    map_external_columns_to_core_solver_columns();
    lean_assert(m_A == nullptr);
    fill_A_from_A_values();
    m_b.resize(m_A->row_count());
}

template <typename T, typename X> void lp_solver<T, X>::count_slacks_and_artificials() {
    for (int i = row_count() - 1; i >= 0; i--) {
        count_slacks_and_artificials_for_row(i);
    }
}

template <typename T, typename X> void lp_solver<T, X>::count_slacks_and_artificials_for_row(unsigned i) {
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

template <typename T, typename X>    T lp_solver<T, X>::low_bound_shift_for_row(unsigned i) {
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

template <typename T, typename X> void lp_solver<T, X>::fill_m_b() {
    for (int i = this->row_count() - 1; i >= 0; i--) {
        lean_assert(this->m_constraints.find(this->m_core_solver_rows_to_external_rows[i]) != this->m_constraints.end());
        unsigned external_i = this->m_core_solver_rows_to_external_rows[i];
        auto & constraint = this->m_constraints[external_i];
        this->m_b[i] = constraint.m_rs - low_bound_shift_for_row(external_i);
    }
}

template <typename T, typename X>    T lp_solver<T, X>::get_column_value_with_core_solver(unsigned column, lp_core_solver_base<T, X> * core_solver) const {
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

template <typename T, typename X> void lp_solver<T, X>::set_scaled_cost(unsigned j) {
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
}
