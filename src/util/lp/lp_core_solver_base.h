/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <string>
#include "util/lp/lp.h"
#include "util/lp/core_solver_pretty_printer.h"
#include <set>
#include <vector>
#include "util/lp/numeric_pair.h"
namespace lean {
    void init_basic_part_of_basis_heading(std::vector<unsigned> & basis, unsigned m, vector<int> & basis_heading) {
    for (unsigned i = 0; i < m; i++) {
        unsigned column = basis[i];
        basis_heading[column] = i;
    }
}

void init_non_basic_part_of_basis_heading(vector<int> & basis_heading, vector<unsigned> & non_basic_columns, unsigned n) {
    for (int j = n; j--;){
        if (basis_heading[j] < 0) {
            non_basic_columns.push_back(j);
             // the index of column j in m_non_basic_columns is (- basis_heading[j] - 1)
            basis_heading[j] = - non_basic_columns.size();
        }
    }
}
void init_basis_heading_and_non_basic_columns_vector(std::vector<unsigned> & basis,
                                                         unsigned m,
                                                         vector<int> & basis_heading,
                                                         unsigned n,
                                                         vector<unsigned> & non_basic_columns) {
    init_basic_part_of_basis_heading(basis, m, basis_heading);
    init_non_basic_part_of_basis_heading(basis_heading, non_basic_columns, n);
}

template <typename T, typename X> // X represents the type of the x variable and the bounds
class lp_core_solver_base {
public:
    unsigned m_m; // it is the length of basis. The matrix m_A has m_m rows and the dimension of the matrix A is m_m
    unsigned m_n; // the number of columns in the matrix m_A
    std::vector<T> m_pivot_row_of_B_1;  // the pivot row of the reverse of B
    std::vector<T> m_pivot_row; // this is the real pivot row of the simplex tableu
    vector<unsigned> m_pivot_row_index;
    static_matrix<T, X> & m_A; // the matrix A
    vector<X> & m_b; // the right side
    std::vector<unsigned> & m_basis;
    std::vector<int> m_basis_heading;
    std::vector<X> & m_x; // a feasible solution, the fist time set in the constructor
    std::vector<T> & m_costs;
    lp_settings & m_settings;
    std::vector<T> m_y; // the buffer for yB = cb
    lp_status m_status;
    // a device that is able to solve Bx=c, xB=d, and change the basis
    lu<T, X> * m_factorization;
    const unordered_map<unsigned, string> & m_column_names;
    indexed_vector<T> m_w; // the vector featuring in 24.3 of the Chvatal book
    std::vector<T> m_d; // the vector of reduced costs
    std::vector<T> m_ed; // the solution of B*m_ed = a
    vector<unsigned>  m_index_of_ed;
    unsigned m_total_iterations = 0;
    int m_start_time;
    unsigned m_iters_with_no_cost_growing = 0;
    vector<unsigned> m_non_basic_columns;
    vector<column_type> & m_column_type;
    vector<X> & m_low_bound_values;
    vector<X> & m_upper_bound_values;
    vector<T> m_column_norms; // the approximate squares of column norms that help choosing a profitable column
    vector<X> m_copy_of_xB;
    unsigned m_refactor_counter = 200;
    lp_core_solver_base(static_matrix<T, X> & A,
                        vector<X> & b, // the right side vector
                        std::vector<unsigned> & basis,
                        std::vector<X> & x,
                        std::vector<T> & costs,
                        lp_settings & settings,
                        const unordered_map<unsigned, string> & column_names,
                        vector<column_type> & column_types,
                        vector<X> & low_bound_values,
                        vector<X> & upper_bound_values):
        m_m(A.row_count()),
        m_n(A.column_count()),
        m_pivot_row_of_B_1(m_m),
        m_pivot_row(m_n, zero_of_type<T>()),
        m_A(A),
        m_b(b),
        m_basis(basis),
        m_x(x),
        m_costs(costs),
        m_settings(settings),
        m_y(m_m),
        m_status(FEASIBLE),
        m_factorization(nullptr),
        m_column_names(column_names),
        m_w(m_m),
        m_d(m_n),
        m_ed(m_m),
        m_column_type(column_types),
        m_low_bound_values(low_bound_values),
        m_upper_bound_values(upper_bound_values),
        m_column_norms(m_n, T(1)),
        m_copy_of_xB(m_m) {
        if (m_m) {
            lean_assert(m_A.col_val_equal_to_row_val());
            init();
            init_basis_heading();
        }
    }

    void allocate_basis_heading() { // the rest of initilization will be handled by the factorization class
        m_basis_heading.clear();
        m_basis_heading.resize(m_n, -1);
    }
    void init() {
        lean_assert(m_costs.size() == m_n);
        lean_assert(m_basis.size() == m_m);
        lean_assert(m_b.size() == m_m);
        allocate_basis_heading();
        init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
        m_refactor_counter = 0;
        srand48(1);
    }

    virtual ~lp_core_solver_base() {
        if (m_factorization != nullptr)
            delete m_factorization;
     }

    vector<unsigned> & non_basis() {
        return m_factorization->m_non_basic_columns;
    }

    void set_status(lp_status status) {
        m_status = status;
    }
    lp_status get_status() {
        return m_status;
    }

    void fill_cb(T * y){
        for (unsigned i = 0; i < m_m; i++) {
            y[i] = m_costs[m_basis[i]];
        }
    }


    void fill_cb(std::vector<T> & y){
        for (unsigned i = 0; i < m_m; i++)
            y[i] = m_costs[m_basis[i]];
    }

    void solve_yB(std::vector<T> & y) {
        fill_cb(y); // now y = cB, that is the projection of costs to basis
        m_factorization->solve_yB(y);
    }

    void update_index_of_ed() {
        m_index_of_ed.clear();
        unsigned i = m_ed.size();
        while (i--) {
            if (!is_zero(m_ed[i]))
                m_index_of_ed.push_back(i);
        }
    }

    void solve_Bd(unsigned entering) {
        m_factorization->solve_Bd(entering, m_ed, m_w);
        update_index_of_ed();
#ifndef NDEBUG
    // auto B = get_B(m_factorization);
    // vector<T>  a(m_m);
    // m_A.copy_column_to_vector(entering, a);
    // vector<T> cd(m_ed);
    // B.apply_from_left(cd, m_settings);
    // lean_assert(vectors_are_equal(cd , a));
#endif
    }

    void pretty_print() {
        core_solver_pretty_printer<T, X> pp(*this);
        pp.print();
    }

    void save_state(T * w_buffer, T * d_buffer) {
        copy_m_w(w_buffer);
        copy_m_ed(d_buffer);
    }

    void restore_state(T * w_buffer, T * d_buffer) {
        restore_m_w(w_buffer);
        restore_m_ed(d_buffer);
    }

    X get_cost() {
        return dot_product(m_costs, m_x, m_n);
    }

    void copy_m_w(T * buffer) {
        unsigned i = m_m;
        while (i --) {
            buffer[i] = m_w[i];
        }
    }

    void restore_m_w(T * buffer) {
        m_w.m_index.clear();
        unsigned i = m_m;
        while (i--) {
            if (!is_zero(m_w[i] = buffer[i]))
                m_w.m_index.push_back(i);
        }
    }

    // needed for debugging
    void copy_m_ed(T * buffer) {
        unsigned i = m_m;
        while (i --) {
            buffer[i] = m_ed[i];
        }
    }

    void restore_m_ed(T * buffer) {
        unsigned i = m_m;
        while (i --) {
            m_ed[i] = buffer[i];
        }
    }

    bool A_mult_x_is_off() {
        if (precise<T>()) {
             return false;
        }

        T feps = convert_struct<T, double>::convert(m_settings.refactor_tolerance);
        X one = convert_struct<X, double>::convert(1.0);
        for (unsigned i = 0; i < m_m; i++) {
            X delta = abs(m_b[i] - m_A.dot_product_with_row(i, m_x));
            X eps = feps * (one + T(0.1) * abs(m_b[i]));

            if (delta >eps) {
                cout << "x is off (";
                cout << "m_b[" << i  << "] = " << m_b[i] << " ";
                cout << "left side = " << m_A.dot_product_with_row(i, m_x) << ' ';
                cout << "delta = " << delta << ' ';
                cout << "iters = " << m_total_iterations << ")" << endl;
                return true;
            }
        }
        return false;
    }
    // from page 182 of Istvan Maros's book
    void calculate_pivot_row_of_B_1(unsigned pivot_row) {
        unsigned i = m_m;
        while (i--) {
            m_pivot_row_of_B_1[i] = numeric_traits<T>::zero();
        }
        m_pivot_row_of_B_1[pivot_row] = numeric_traits<T>::one();
        m_factorization->solve_yB(m_pivot_row_of_B_1);
    }

    void zero_pivot_row() {
        for (unsigned j : m_pivot_row_index)
            m_pivot_row[j] = numeric_traits<T>::zero();
        m_pivot_row_index.clear();
    }

    void calculate_pivot_row_when_pivot_row_of_B1_is_ready() {
        zero_pivot_row();
        int i = m_m;
        while (i--) {
            T pi_1 = m_pivot_row_of_B_1[i];
            if (numeric_traits<T>::is_zero(pi_1)) {
                continue;
            }
            for (auto & c : m_A.m_rows[i]) {
                unsigned j = c.m_j;
                if (m_factorization->m_basis_heading[j] < 0) {
                    m_pivot_row[j] += c.get_val() * pi_1;
                }
            }
        }

        unsigned j = m_pivot_row.size();
        while (j--) {
            if (!is_zero(m_pivot_row[j]))
                m_pivot_row_index.push_back(j);
        }
    }

    void update_x(unsigned entering, X delta) {
        if (is_zero(delta)) {
            return;
        }
        m_x[entering] += delta;
        for (unsigned i : m_index_of_ed) {
            m_copy_of_xB[i] = m_x[m_basis[i]];
            m_x[m_basis[i]] -= delta * m_ed[i];
        }
    }

    T get_var_value(unsigned j) const {
        return m_x[j];
    }

    void print_statistics(X cost) {
        cout << "cost = " << T_to_string(cost) <<
            ", nonzeros = " << m_factorization->get_number_of_nonzeroes() << endl;
    }

    bool print_statistics_with_iterations_and_check_that_the_time_is_over(unsigned total_iterations) {
        if (total_iterations % m_settings.report_frequency == 0) {
            cout << "iterations = " << total_iterations  <<  ", nonzeros = " << m_factorization->get_number_of_nonzeroes() << endl;
            if (time_is_over()) {
                return true;
            }
        }
        return false;
    }

    bool print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(string str, unsigned total_iterations) {
        if (total_iterations % m_settings.report_frequency == 0) {
            cout << str << " iterations = " << total_iterations  <<  " cost = " << T_to_string(get_cost()) <<", nonzeros = " << m_factorization->get_number_of_nonzeroes() << endl;
            if (time_is_over()) {
                return true;
            }
        }
        return false;
    }

    bool print_statistics_with_cost_and_check_that_the_time_is_over(unsigned total_iterations, X cost) {
        if (total_iterations % m_settings.report_frequency == 0) {
            cout << "iterations = " << total_iterations  <<  ", ";
            print_statistics(cost);
            if (time_is_over()) {
                return true;
            }
        }
        return false;
    }

    bool print_statistics_and_check_that_the_time_is_over(unsigned total_iterations) {
        if (total_iterations % (numeric_traits<T>::precise()? static_cast<unsigned>(m_settings.report_frequency/10) : m_settings.report_frequency) == 0) {
            cout << "iterations = " << total_iterations  <<  ", ";
            if (time_is_over()) {
                return true;
            }
        }
        return false;
    }

    void set_non_basic_x_to_correct_bounds() {
        for (unsigned j : non_basis()) {
            switch (m_column_type[j]) {
            case boxed:
                m_x[j] = m_d[j] < 0? m_upper_bound_values[j]: m_low_bound_values[j];
                break;
            case low_bound:
                m_x[j] = m_low_bound_values[j];
                lean_assert(column_is_dual_feasible(j));
                break;
            case upper_bound:
                m_x[j] = m_upper_bound_values[j];
                lean_assert(column_is_dual_feasible(j));
                break;
            default:
                break;
            }
        }
    }
    bool at_bound(const X &x, const X & bound) const {
        return !below_bound(x, bound) && !above_bound(x, bound);
    }

    bool below_bound(const X & x, const X & bound) const {
        if (precise<X>()) return x < bound;
        return below_bound_numeric<X>(x, bound, m_settings.primal_feasibility_tolerance);
    }

    bool above_bound(const X & x, const X & bound) const {
        if (precise<X>()) return x > bound;
        return above_bound_numeric<X>(x, bound, m_settings.primal_feasibility_tolerance);
    }

    bool x_below_low_bound(unsigned p) {
        return below_bound(m_x[p], m_low_bound_values[p]);
    }

    bool x_above_upper_bound(unsigned p) {
        return above_bound(m_x[p], m_upper_bound_values[p]);
    }


    bool x_is_at_low_bound(unsigned j) const {
        return at_bound(m_x[j], m_low_bound_values[j]);
    }
    bool x_is_at_upper_bound(unsigned j) const {
        return at_bound(m_x[j], m_upper_bound_values[j]);
    }

    bool x_is_at_bound(unsigned j) const {
        return x_is_at_low_bound(j) || x_is_at_upper_bound(j);
    }

    bool column_is_dual_feasible(unsigned j) {
        switch (m_column_type[j]) {
        case fixed:
        case boxed:
            return (x_is_at_low_bound(j) && d_is_not_negative(j)) ||
                (x_is_at_upper_bound(j) && d_is_not_positive(j));
        case low_bound:
            return x_is_at_low_bound(j) && d_is_not_negative(j);
        case upper_bound:
            cout << "upper_bound type should be switched to low_bound" << endl;
            lean_assert(false); // impossible case
        case free_column:
            return numeric_traits<X>::is_zero(m_d[j]);
        default:
            cout << "column = " << j << endl;
            cout << "unexpected column type = " << column_type_to_string(m_column_type[j]) << endl;
            lean_assert(false);
            throw "unexpected column type";
            break;
        }
    }
    bool d_is_not_negative(unsigned j) {
        if (numeric_traits<T>::precise()) {
            return m_d[j] >= numeric_traits<T>::zero();
        }
        return m_d[j] > -T(0.00001);
    }

    bool d_is_not_positive(unsigned j) {
        if (numeric_traits<T>::precise()) {
            return m_d[j] <= numeric_traits<T>::zero();
        }
        return m_d[j] < T(0.00001);
    }


    bool time_is_over() {
        int span_in_mills = get_millisecond_span(m_start_time);
        if (span_in_mills / 1000.0  > m_settings.time_limit) {
            cout << "time is over" << endl;
            return true;
        }
        return false;
    }

    void rs_minus_Anx(vector<X> & rs) {
        unsigned row = m_m;
        while (row--) {
            auto &rsv = rs[row] = m_b[row];
            for (auto & it : m_A.m_rows[row]) {
                unsigned j = it.m_j;
                if (m_basis_heading[j] < 0) {
                    rsv -= m_x[j] * it.get_val();
                }
            }
        }
    }

    bool find_x_by_solving() {
        solve_Ax_eq_b();
        bool ret=  !A_mult_x_is_off();
        if (ret)
            cout << "find_x_by_solving succeeded" << endl;
        else
            cout << "find_x_by_solving did not succeed" << endl;
        return ret;
    }

    bool update_basis_and_x(int entering, int leaving, X const & tt) {
        if (!is_zero(tt)) {
            update_x(entering, tt);
            if (A_mult_x_is_off() && !find_x_by_solving()) {
                init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
                m_refactor_counter = 0;

                if (!find_x_by_solving()) {
                    restore_x(entering, tt);
                    lean_assert(!A_mult_x_is_off());
                    init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
                    m_refactor_counter = 0;
                    m_iters_with_no_cost_growing++;
                    if (m_factorization->get_status() != LU_status::OK) {
                        cout << "failing refactor on off_result for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << m_total_iterations << endl;
                        throw "";
                    }
                    return false;
                }
            }
        }

        bool refactor = m_refactor_counter++ >= 200;
        if (!refactor) {
           const T &  pivot = this->m_pivot_row[entering]; // m_ed[m_factorization->basis_heading(leaving)] is the same but the one that we are using is more precise
             m_factorization->replace_column(leaving, pivot, m_w);
            if (m_factorization->get_status() == LU_status::OK) {
                m_factorization->change_basis(entering, leaving);
                return true;
            }
        }
        // need to refactor
        m_refactor_counter = 0;
        m_factorization->change_basis(entering, leaving);
        init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
        if (m_factorization->get_status() != LU_status::OK || A_mult_x_is_off()) {
            cout << "failing refactor for entering = " << entering << ", leaving = " << leaving << " total_iterations = " << m_total_iterations << endl;
            restore_x_and_refactor(entering, leaving, tt);
            lean_assert(!A_mult_x_is_off());
            m_iters_with_no_cost_growing++;
            cout << "rolled back after failing of init_factorization()" << endl;
            m_status = UNSTABLE;
            return false;
        }
        return true;
    }


    void init_basis_heading() {
        init_basis_heading_and_non_basic_columns_vector(m_basis, m_m, m_basis_heading, m_n, m_non_basic_columns);
        lean_assert(basis_heading_is_correct());
    }

    bool basis_has_no_doubles() {
        std::set<unsigned> bm;
        for (unsigned i = 0; i < m_m; i++) {
            bm.insert(m_basis[i]);
        }
        return bm.size() == m_m;
    }

    bool non_basis_has_no_doubles() {
        std::set<int> bm;
        for (auto j : m_non_basic_columns) {
            bm.insert(j);
        }
        return bm.size() == m_non_basic_columns.size();
    }

    bool basis_is_correctly_represented_in_heading() {
        for (unsigned i = 0; i < m_m; i++) {
            if (m_basis_heading[m_basis[i]] != i)
                return false;
        }
        return true;
    }
    bool non_basis_is_correctly_represented_in_heading() {
        for (int i = 0; i < m_non_basic_columns.size(); i++) {
            if (m_basis_heading[m_non_basic_columns[i]] !=  - i - 1)
                return false;
        }
        for (int j = 0; j < m_A.column_count(); j++) {
            if (m_basis_heading[j] >= 0) {
                lean_assert(m_basis_heading[j] < m_A.row_count() && m_basis[m_basis_heading[j]] == j);
            }
        }
        return true;
    }

    bool basis_heading_is_correct() {
        return basis_has_no_doubles() && non_basis_has_no_doubles() && basis_is_correctly_represented_in_heading() && non_basis_is_correctly_represented_in_heading();
    }

    void restore_x_and_refactor(int entering, int leaving, X const & t) {
        m_factorization->restore_basis_change(entering, leaving);
        restore_x(entering, t);
        init_factorization(m_factorization, m_A, m_basis, m_basis_heading, m_settings, m_non_basic_columns);
        if (m_factorization->get_status() == LU_status::Degenerated) {
            cout << "cannot refactor" << endl;
            m_status = lp_status::FLOATING_POINT_ERROR;
        }
        //   solve_Ax_eq_b();
        if (A_mult_x_is_off()) {
            cout << "cannot restore solution" << endl;
            m_status = lp_status::FLOATING_POINT_ERROR;
            return;
        }
    }

    void restore_x(unsigned entering, X const & t) {
        if (is_zero(t)) return;
        cout << "calling restore for entering " << entering << endl;
        m_x[entering] -= t;
        for (unsigned i : m_index_of_ed) {
            m_x[m_basis[i]]  = m_copy_of_xB[i];
        }
    }

    void fill_reduced_costs_from_m_y_by_rows() {
        unsigned j = m_n;
        while (j--) {
            if (m_factorization->m_basis_heading[j] < 0)
                m_d[j] = m_costs[j];
            else
                m_d[j] = numeric_traits<T>::zero();
        }

        unsigned i = m_m;
        while (i--) {
            const T & y = m_y[i];
            if (is_zero(y)) continue;
            for (auto & it : m_A.m_rows[i]) {
                j = it.m_j;
                if  (m_factorization->m_basis_heading[j] < 0)
                    m_d[j] -= y * it.get_val();
            }
        }
    }

    void copy_rs_to_xB(vector<X> & rs) {
        unsigned j = m_m;
        while (j--) {
            m_x[m_basis[j]] = rs[j];
        }
    }
    virtual bool low_bounds_are_set() const { return false; }
    X low_bound_value(unsigned j) const { return m_low_bound_values[j]; }
    X upper_bound_value(unsigned j) const { return m_upper_bound_values[j]; }

    column_type get_column_type(unsigned j) const {return m_column_type[j]; }

    bool pivot_row_element_is_too_small_for_ratio_test(unsigned j) {
        return m_settings.abs_val_is_smaller_than_pivot_tolerance(m_pivot_row[j]);
    }

    X bound_span(unsigned j) {
        return m_upper_bound_values[j] - m_low_bound_values[j];
    }

    std::string column_name(unsigned column) const {
        auto it = m_column_names.find(column);
        if (it == m_column_names.end()) {
            std::string name = T_to_string(column);
            return std::string(string("u") + name);
        }
        return it->second;
    }

    void copy_right_side(vector<X> & rs) {
        unsigned i = m_m;
        while (i --) {
            rs[i] = m_b[i];
        }
    }

    void add_delta_to_xB(vector<X> & del) {
        unsigned i = m_m;
        while (i--) {
            this->m_x[this->m_basis[i]] -= del[i];
        }
    }

    void find_error_in_BxB(vector<X>& rs){
        unsigned row = m_m;
        while (row--) {
            auto &rsv = rs[row];
            for (auto & it : m_A.m_rows[row]) {
                unsigned j = it.m_j;
                if (m_basis_heading[j] >= 0) {
                    rsv -= m_x[j] * it.get_val();
                }
            }
        }
    }

    // recalculates the projection of x to B, such that Ax = b, whereab is the right side
    void solve_Ax_eq_b() {
        vector<X> rs(m_m);
        rs_minus_Anx(rs);
        vector<X> rrs = rs; // another copy of rs
        m_factorization->solve_By(rs);
        copy_rs_to_xB(rs);
        find_error_in_BxB(rrs);
        m_factorization->solve_By(rrs);
        add_delta_to_xB(rrs);
    }

    void snap_non_basic_x_to_bound() {
        for (unsigned j : non_basis()) {
            switch (m_column_type[j]) {
            case fixed:
            case boxed:
                if (x_is_at_bound(j))
                    break; // we should preserve x if possible
                m_x[j] = m_low_bound_values[j];
                break;
            case low_bound:
                if (x_is_at_low_bound(j))
                    break;
                m_x[j] = m_low_bound_values[j];
                break;
            case upper_bound:
                if (x_is_at_upper_bound(j))
                    break;
                m_x[j] = m_upper_bound_values[j];
                break;
            default:
                break;
            }
        }
    }
    void snap_non_basic_x_to_bound_and_free_to_zeroes() {
        for (unsigned j : non_basis()) {
            lean_assert(j < m_x.size());
            switch (m_column_type[j]) {
            case fixed:
            case boxed:
            case low_bound:
                m_x[j] = m_low_bound_values[j];
                break;
            case upper_bound:
                m_x[j] = m_upper_bound_values[j];
                break;
            default:
                m_x[j] = zero_of_type<X>();
                break;
            }
        }
    }
    void snap_xN_to_bounds() {
        snap_non_basic_x_to_bound();
        solve_Ax_eq_b();
    }

    void snap_xN_to_bounds_and_free_columns_to_zeroes() {
        snap_non_basic_x_to_bound_and_free_to_zeroes();
        solve_Ax_eq_b();
    }

    void init_reduced_costs_for_one_iteration() {
        solve_yB(m_y);
        fill_reduced_costs_from_m_y_by_rows();
    }

    non_basic_column_value_position get_non_basic_column_value_position(unsigned j) {
        switch (m_column_type[j]) {
        case fixed:
            return at_fixed;
        case free_column:
            return free_of_bounds;
        case boxed:
            return x_is_at_low_bound(j)? at_low_bound : at_upper_bound;
        case low_bound:
            return at_low_bound;
        case upper_bound:
            return at_upper_bound;
        default:
            throw "unexpected column type";
        }
    }
};
}
