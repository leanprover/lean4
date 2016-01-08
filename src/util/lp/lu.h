/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once

#include <vector>
#include "util/debug.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include <algorithm>
#include <set>
#include "util/lp/sparse_matrix.h"
#include "util/lp/static_matrix.h"
#include <string>
#include "util/lp/numeric_pair.h"
#include <iostream>
#include <fstream>
#include "util/lp/row_eta_matrix.h"
#include "util/lp/square_dense_submatrix.h"
namespace lean {
template <typename T>
std::string T_to_string(const T & t); // forward definition
#ifdef LEAN_DEBUG
template <typename T, typename X> // print the nr x nc submatrix at the top left corner
void print_submatrix(sparse_matrix<T, X> & m, unsigned mr, unsigned nc) {
    std::vector<std::vector<std::string>> A;
    std::vector<unsigned> widths;
    for (unsigned i = 0; i < m.row_count() && i < mr ; i++) {
        A.push_back(std::vector<std::string>());
        for (unsigned j = 0; j < m.column_count() && j < nc; j++) {
            A[i].push_back(T_to_string(static_cast<T>(m(i, j))));
        }
    }

    for (unsigned j = 0; j < m.column_count() && j < nc; j++) {
        widths.push_back(get_width_of_column(j, A));
    }

    print_matrix_with_widths(A, widths);
}

template<typename T, typename X>
void print_matrix(static_matrix<T, X> &m) {
    std::vector<std::vector<std::string>> A;
    std::vector<unsigned> widths;
    std::set<pair<unsigned, unsigned>> domain = m.get_domain();
    for (unsigned i = 0; i < m.row_count(); i++) {
        A.push_back(std::vector<std::string>());
        for (unsigned j = 0; j < m.column_count(); j++) {
            A[i].push_back(T_to_string(static_cast<T>(m(i, j))));
        }
    }

    for (unsigned j = 0; j < m.column_count(); j++) {
        widths.push_back(get_width_of_column(j, A));
    }

    print_matrix_with_widths(A, widths);
}

template <typename T, typename X>
void print_matrix(sparse_matrix<T, X>& m) {
    std::vector<std::vector<std::string>> A;
    std::vector<unsigned> widths;
    for (unsigned i = 0; i < m.row_count(); i++) {
        A.push_back(std::vector<std::string>());
        for (unsigned j = 0; j < m.column_count(); j++) {
            A[i].push_back(T_to_string(static_cast<T>(m(i, j))));
        }
    }

    for (unsigned j = 0; j < m.column_count(); j++) {
        widths.push_back(get_width_of_column(j, A));
    }

    print_matrix_with_widths(A, widths);
}
#endif

enum class LU_status { OK, Degenerated};

template <typename T, typename X>
X dot_product(const std::vector<T> & a, const std::vector<X> & b, unsigned l) {
    auto r = zero_of_type<X>();
    for (unsigned i = 0; i < l; i++) {
        r += a[i] * b[i];
    }
    return r;
}


template <typename T, typename X>
class one_elem_on_diag: public tail_matrix<T, X> {
    unsigned m_i;
    T m_val;
public:
    one_elem_on_diag(unsigned i, T val) : m_i(i), m_val(val) {
#ifdef LEAN_DEBUG
        m_one_over_val = numeric_traits<T>::one() / m_val;
#endif
    }

    one_elem_on_diag(const one_elem_on_diag & o) {
        m_i = o.m_i;
        m_val = o.m_val;

#ifdef LEAN_DEBUG
        m_m = m_n = o.m_m;
        m_one_over_val = numeric_traits<T>::one() / o.m_val;
#endif
    }

#ifdef LEAN_DEBUG
    unsigned m_m;
    unsigned m_n;
    virtual void set_number_of_rows(unsigned m) { m_m = m; m_n = m; }
    virtual void set_number_of_columns(unsigned n) { m_m = n; m_n = n; }
    T m_one_over_val;

    T get_elem (unsigned i, unsigned j) const {
        if (i == j){
            if (j == m_i) {
                return m_one_over_val;
            }
            return numeric_traits<T>::one();
        }

        return numeric_traits<T>::zero();
    }

    unsigned row_count() const { return m_m; } // not defined }
    unsigned column_count() const { return m_m; } // not defined  }
#endif
    void apply_from_left(std::vector<X> & w, lp_settings &) {
        w[m_i] /= m_val;
    }

    void apply_from_right(std::vector<T> & w) {
        w[m_i] /= m_val;
    }

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
        w[m_i] /= m_val;
        if (settings.abs_val_is_smaller_than_drop_tolerance(w[m_i])) { // todo : is it needed?
            w.erase_from_index(m_i);
            w[m_i] = numeric_traits<T>::zero();
        }
    }

    void conjugate_by_permutation(permutation_matrix<T, X> & p) {
        // this = p * this * p(-1)
#ifdef LEAN_DEBUG
        // auto rev = p.get_reverse();
        // auto deb = ((*this) * rev);
        // deb = p * deb;
#endif
        m_i = p.apply_reverse(m_i);

#ifdef LEAN_DEBUG
        // lean_assert(*this == deb);
#endif
    }
}; // end of one_elem_on_diag

    // This class supports updates of the columns of B, and solves systems Bx=b,and yB=c
    // Using Suhl-Suhl method described in the dissertation of Achim Koberstein, Chapter 5


template <typename T, typename X>
class lu {
    LU_status m_status = LU_status::OK;
public:
    // the fields
    unsigned m_dim;
    static_matrix<T, X> const &m_A;
    std::vector<unsigned>& m_basis;
    permutation_matrix<T, X> m_Q;
    permutation_matrix<T, X> m_R;
    sparse_matrix<T, X> m_U;
    square_dense_submatrix<T, X>* m_dense_LU;

    // m_tail is composed of tail_matrices:
    // one_off_diagonal_matrix, and transposition_matrix
    std::vector<tail_matrix<T, X> *> m_tail;
    lp_settings & m_settings;
    std::vector<int> & m_basis_heading;
    bool m_failure = false;
    std::vector<unsigned> & m_non_basic_columns;
    indexed_vector<T>  m_row_eta_work_vector;
    // constructor
    // if A is an m by n matrix then basis has length m and values in [0,n); the values are all different
    // they represent the set of m columns
    lu(static_matrix<T, X> const & A,
       std::vector<unsigned>& basis,
       std::vector<int> & basis_heading,
       lp_settings & settings,
       std::vector<unsigned> & non_basic_columns):
        m_dim(A.row_count()),
        m_A(A),
        m_basis(basis),
        m_Q(m_dim),
        m_R(m_dim),
        m_U(A, basis), // create the square matrix that eventually will be factorized
        m_settings(settings),
        m_basis_heading(basis_heading),
        m_non_basic_columns(non_basic_columns),
        m_row_eta_work_vector(A.row_count()){
#ifdef LEAN_DEBUG
        debug_test_of_basis(A, basis);
#endif
        create_initial_factorization();
        if (get_status() != LU_status::OK) {
            if (get_status() == LU_status::Degenerated) {
                std::cout << "lu status is Degenerated" << std::endl;
            } else {
                std::cout << "lu status is " <<static_cast<int>(get_status()) << std::endl;
            }
            return;
        }
#ifdef LEAN_DEBUG
        // lean_assert(check_correctness());
#endif
    }

    void debug_test_of_basis(static_matrix<T, X> const & A, std::vector<unsigned> & basis) {
        std::set<unsigned> set;
        for (unsigned i = 0; i < A.row_count(); i++) {
            lean_assert(basis[i]< A.column_count());
            set.insert(basis[i]);
        }
        lean_assert(set.size() == A.row_count());
    }


    unsigned non_basic_column_index_in_non_basic_columns(unsigned j) {
        return - m_basis_heading[j] - 1;
    }

    void solve_By(std::vector<X> & y) {
        init_vector_y(y);
        solve_By_when_y_is_ready(y);
    }

    void solve_Bd_when_w_is_ready(std::vector<T> & d, indexed_vector<T>& w ) { // w -  the vector featuring in 24.3
        for (int i = m_dim - 1; i >= 0; i--) {  // index ? todo
            d[i] = w[i];
        }
        solve_By_when_y_is_ready(d);
    }

    template <typename L>
    void solve_By_when_y_is_ready(std::vector<L> & y) {
        m_U.double_solve_U_y(y);
        m_R.apply_reverse_from_left(y); // see 24.3 from Chvatal
        if (precise<X>()) return;
        unsigned i = m_dim;
        while (i--) {
            if (is_zero(y[i])) continue;
            if (m_settings.abs_val_is_smaller_than_drop_tolerance(y[i])){
                y[i] = zero_of_type<L>();
            }
        }
    }


    void print_indexed_vector(indexed_vector<T> & w, std::ofstream & f) {
        f << "vector_start" << std::endl;
        for (unsigned j : w.m_index) {
            f << j << " " << w[j] << std::endl;
        }
        f << "vector_end" << std::endl;
    }
    void print_basis(std::ofstream & f) {
        f << "basis_start" << std::endl;
        for (unsigned j : m_basis)
            f << j << std::endl;
        f << "basis_end" << std::endl;
    }
    void print_matrix_compact(std::ofstream & f) {
        f << "matrix_start" << std::endl;
        f << "nrows " << m_A.row_count() << std::endl;
        f << "ncolumns " << m_A.column_count() << std::endl;
        for (unsigned i = 0; i < m_A.row_count(); i++) {
            auto & row = m_A.m_rows[i];
            f << "row " << i << std::endl;
            for (auto & t : row.m_cells) {
                f << "column " << t.m_j << " value " << t.m_value << std::endl;
            }
            f << "row_end" << std::endl;
        }
        f << "matrix_end" << std::endl;
    }

    void print(indexed_vector<T> & w) {
        std::string dump_file_name("/tmp/lu");
        remove(dump_file_name.c_str());
        std::ofstream f(dump_file_name);
        if (!f.is_open()) {
            std::cout << "cannot open file " << dump_file_name << std::endl;
            return;
        }
        std::cout << "writing lu dump to " << dump_file_name << std::endl;
        print_matrix_compact(f);
        print_basis(f);
        print_indexed_vector(w, f);
        f.close();
    }

    void solve_Bd(unsigned a_column, std::vector<T> & d, indexed_vector<T> & w) {
        init_vector_w(a_column, w);
        solve_Bd_when_w_is_ready(d, w);
    }

    bool column_can_be_taken_to_basis(unsigned i) {
        return m_basis_heading[i] < 0;
    }

    void  solve_yB_internal(std::vector<T>& y) {
        // first solve yU = cb*R(-1)
        m_R.apply_reverse_from_right(y); // got y = cb*R(-1)
        m_U.solve_y_U(y); // got y*U=cb*R(-1)
        m_Q.apply_reverse_from_right(y); //
        for (auto e = m_tail.rbegin(); e != m_tail.rend(); ++e) {
#ifdef LEAN_DEBUG
            (*e)->set_number_of_columns(m_dim);
#endif
            (*e)->apply_from_right(y);
        }
    }

    void add_delta_to_solution(std::vector<T>& yc, std::vector<T>& y){
        unsigned i = y.size();
        while (i--)
            y[i]+=yc[i];
    }

    void find_error_of_yB(std::vector<T>& yc, const std::vector<T>& y) {
        unsigned i = m_dim;
        while (i--) {
            yc[i] -= m_A.dot_product_with_column(y, m_basis[i]);
        }
    }

    // solves y*B = y
    // y is the input

    void solve_yB(std::vector<T> & y) {
        std::vector<T> yc(y); // copy y aside
        solve_yB_internal(y);
        find_error_of_yB(yc, y);
        solve_yB_internal(yc);
        add_delta_to_solution(yc, y);
    }

    void apply_Q_R_to_U(permutation_matrix<T, X> & r_wave) {
        m_U.multiply_from_right(r_wave);
        m_U.multiply_from_left_with_reverse(r_wave);
    }

    void change_basis(unsigned entering, unsigned leaving) {
        lean_assert(entering < m_A.column_count() && leaving < m_A.column_count());
        int place_in_basis =  m_basis_heading[leaving];
        int place_in_non_basis = - m_basis_heading[entering] - 1;
        lean_assert(0 <= place_in_basis && place_in_basis < m_A.column_count());
        m_basis_heading[entering] = place_in_basis;
        m_basis_heading[leaving] = -place_in_non_basis - 1;
        m_basis[place_in_basis] = entering;
        m_non_basic_columns[place_in_non_basis] = leaving;
    }

    void restore_basis_change(unsigned entering, unsigned leaving) {
        if (m_basis_heading[entering] < 0) {
            return; // the basis has not been changed
        }
        change_basis(leaving, entering);
    }

    LU_status get_status() { return m_status; }

    void set_status(LU_status status) { m_status = status; }

    // Solving yB = cb to find the entering variable,
    // where cb is the cost vector projected to B.
    // The result is stored in cb.

    // solving Bd = a ( to find the column d of B^{-1} A_N corresponding to the entering
    // variable

    ~lu(){
        for (auto t : m_tail) {
            delete t;
        }
    }

    T B(unsigned i, unsigned j) {
        return m_A(i, m_basis[j]);
    }

    void init_vector_y(std::vector<X> & y) {
        apply_lp_lists_to_y(y);
        m_Q.apply_reverse_from_left(y);
    }


    void perform_transformations_on_w(indexed_vector<T>& w) {
        apply_lp_lists_to_w(w);
        m_Q.apply_reverse_from_left(w);
        lean_assert(numeric_traits<T>::precise() || check_vector_for_small_values(w, m_settings));
    }

    // see Chvatal 24.3
    void init_vector_w(unsigned entering, indexed_vector<T> & w) {
        w.clear();
        m_A.copy_column_to_vector(entering, w); // w = a, the column
        perform_transformations_on_w(w);
    }

    void apply_lp_lists_to_w(indexed_vector<T> & w) {
        for (unsigned i = 0; i < m_tail.size(); i++) {
            m_tail[i]->apply_from_left_to_T(w, m_settings);
            lean_assert(check_vector_for_small_values(w, m_settings));
        }
    }

    void apply_lp_lists_to_y(std::vector<X>& y) {
        for (unsigned i = 0; i < m_tail.size(); i++) {
            m_tail[i]->apply_from_left(y, m_settings);
        }
    }

    void swap_rows(int j, int k) {
        if (j != k) {
            m_Q.transpose_from_left(j, k);
            m_U.swap_rows(j, k);
        }
    }

    void swap_columns(int j, int pivot_column) {
        if (j == pivot_column)
            return;
        m_R.transpose_from_right(j, pivot_column);
        m_U.swap_columns(j, pivot_column);
    }

    void push_matrix_to_tail(tail_matrix<T, X>* tm) {
        m_tail.push_back(tm);
    }

    bool pivot_the_row(int row) {
        eta_matrix<T, X> * eta_matrix = get_eta_matrix_for_pivot(row);
        if (eta_matrix == nullptr) {
            m_U.shorten_active_matrix(row, nullptr);
            return true;
        }
        if (!m_U.pivot_with_eta(row, eta_matrix, m_settings))
            return false;
        eta_matrix->conjugate_by_permutation(m_Q);
        push_matrix_to_tail(eta_matrix);
        return true;
    }
    // we're processing the column j now
    eta_matrix<T, X> * get_eta_matrix_for_pivot(unsigned j) {
        eta_matrix<T, X> *ret;
        m_U.fill_eta_matrix(j, &ret);
        return ret;
    }
    // we're processing the column j now
    eta_matrix<T, X> * get_eta_matrix_for_pivot(unsigned j, sparse_matrix<T, X>& copy_of_U) {
        eta_matrix<T, X> *ret;
        copy_of_U.fill_eta_matrix(j, &ret);
        return ret;
    }

    void print_basis() {
        std::cout << "basis ";
        for (unsigned i = 0; i < m_dim; i++) {
            std::cout << m_basis[i] << " ";
        }
        std::cout << std::endl;
    }

    void print_basis_heading() {
        print_basis();
        for (unsigned i = 0; i < m_A.column_count(); i++) {
            std::cout << m_basis_heading[i] << ",";
        }
        std::cout << std::endl;
    }

    // see page 407 of Chvatal
    unsigned transform_U_to_V_by_replacing_column(unsigned leaving, indexed_vector<T> & w) {
        int leaving_column = m_basis_heading[leaving];
        // std::cout << "leaving_column = " << leaving_column << std::endl;
        unsigned column_to_replace = m_R.apply_reverse(leaving_column);
        // std::cout << "leaving_column modified = " << column_to_replace << std::endl;
        m_U.replace_column(column_to_replace, w, m_settings);
        return column_to_replace;
    }

#ifdef LEAN_DEBUG
    void check_vector_w(unsigned entering) {
        T * w = new T[m_dim];
        m_A.copy_column_to_vector(entering, w);
        check_apply_lp_lists_to_w(w);
        delete [] w;
    }

    void check_apply_matrix_to_vector(matrix<T, X> *lp, T *w) {
        if (lp != nullptr) {
            lp -> set_number_of_rows(m_dim);
            lp -> set_number_of_columns(m_dim);
            apply_to_vector(*lp, w);
        }
    }

    void check_apply_lp_lists_to_w(T * w) {
        for (unsigned i = 0; i < m_tail.size(); i++) {
            check_apply_matrix_to_vector(m_tail[i], w);
        }
        permutation_matrix<T, X> qr = m_Q.get_reverse();
        apply_to_vector(qr, w);
        for (int i = m_dim - 1; i >= 0; i--) {
            lean_assert(abs(w[i] - w[i]) < 0.0000001);
        }
    }

    // provide some access operators for testing
    permutation_matrix<T, X> & Q() { return m_Q; }
    permutation_matrix<T, X> & R() { return m_R; }
    matrix<T, X> & U() { return m_U; }
    unsigned tail_size() { return m_tail.size(); }

    tail_matrix<T, X> * get_lp_matrix(unsigned i) {
        return m_tail[i];
    }

    T B_(unsigned i, unsigned j) {
        return m_A.get_elem(i, m_basis[j]);
    }

    unsigned dimension() { return m_dim; }

#endif

    void mark_fixed_variable(unsigned column) {
        m_basis_heading[column] = -2;
    }

    unsigned get_number_of_nonzeroes() {
        return m_U.get_number_of_nonzeroes();
    }


    void process_column(int j) {
        unsigned pi, pj;
        m_U.get_pivot_for_column(pi, pj, T(m_settings.c_partial_pivoting), j);
        if (pi == -1) {
            std::cout << "cannot find the pivot for column " << j << std::endl;
            m_failure = true;
            return;
        }
        swap_columns(j, pj);
        swap_rows(j, pi);
        if (!pivot_the_row(j)) {
            std::cout << "pivot_the_row(" << j << ") failed" << std::endl;
            m_failure = true;
        }
    }

    bool is_correct() {
#ifdef LEAN_DEBUG
        if (get_status() != LU_status::OK) {
            return false;
        }
        dense_matrix<T, X> left_side = get_left_side();
        dense_matrix<T, X> right_side = get_right_side();
        return left_side == right_side;
#else
        return true;
#endif
    }

    int basis_heading(unsigned j) {
        lean_assert(j < m_A.column_count());
        return m_basis_heading[j];
    }

#ifdef LEAN_DEBUG
    dense_matrix<T, X> tail_product() {
        lean_assert(tail_size() > 0);
        dense_matrix<T, X> left_side = permutation_matrix<T, X>(m_dim);
        for (unsigned i = 0; i < tail_size(); i++) {
            matrix<T, X>* lp =  get_lp_matrix(i);
            lp->set_number_of_rows(m_dim);
            lp->set_number_of_columns(m_dim);
            left_side = ((*lp) * left_side);
        }
        return left_side;
    }
    dense_matrix<T, X>  get_left_side() {
        dense_matrix<T, X> left_side = get_B(*this);
        for (unsigned i = 0; i < tail_size(); i++) {
            matrix<T, X>* lp =  get_lp_matrix(i);
            lp->set_number_of_rows(m_dim);
            lp->set_number_of_columns(m_dim);
            left_side = ((*lp) * left_side);
        }
        return left_side;
    }

    dense_matrix<T, X>  get_right_side() {
        auto ret = U() * R();
        ret = Q() * ret;
        return ret;
    }
#endif

    // needed for debugging purposes
    void copy_w(T *buffer, indexed_vector<T> & w) {
        unsigned i = m_dim;
        while (i--) {
            buffer[i] = w[i];
        }
    }

    // needed for debugging purposes
    void restore_w(T *buffer, indexed_vector<T> & w) {
        unsigned i = m_dim;
        while (i--) {
            w[i] = buffer[i];
        }
    }
    bool all_columns_and_rows_are_active() {
        unsigned i = m_dim;
        while (i--) {
            lean_assert(m_U.col_is_active(i));
            lean_assert(m_U.row_is_active(i));
        }
        return true;
    }

    bool too_dense(unsigned j) const {
        unsigned r = m_dim - j;
        if (r < 5)
            return false;
        return r * r * m_settings.density_threshold <= m_U.get_number_of_nonzeroes_below_row(j);
    }

    void pivot_in_dense_mode(unsigned i) {
        int j = m_dense_LU->find_pivot_column_in_row(i);
        if (j == -1) {
            m_failure = true;
            return;
        }
        if (i != j) {
            swap_columns(i, j);
            m_dense_LU->swap_columns(i, j);
        }
        m_dense_LU->pivot(i, m_settings);
    }

    void create_initial_factorization(){
        m_U.prepare_for_factorization();
        unsigned j;
        for (j = 0; j < m_dim; j++) {
            process_column(j);
            if (m_failure || too_dense(j + 1)) {
                break;
            }
        }
        if (m_failure) {
            set_status(LU_status::Degenerated);
            return;
        }
        if (j == m_dim) {
            lean_assert(m_U.is_upper_triangular_and_maximums_are_set_correctly_in_rows(m_settings));
            return;
        }
        j++;
        //        std::cout << "switching to dense factoring for " << j << endl;
        m_dense_LU = new square_dense_submatrix<T, X>(&m_U, j);
        for (; j < m_dim; j++) {
            pivot_in_dense_mode(j);
            if (m_failure) {
                set_status(LU_status::Degenerated);
                return;
            }
        }
        m_dense_LU->update_parent_matrix(m_settings);
        lean_assert(m_dense_LU->is_L_matrix());
        m_dense_LU->conjugate_by_permutation(m_Q);
        push_matrix_to_tail(m_dense_LU);
        // lean_assert(is_correct());
        // lean_assert(m_U.is_upper_triangular_and_maximums_are_set_correctly_in_rows(m_settings));
    }

    void calculate_r_wave_and_update_U(unsigned bump_start, unsigned bump_end, permutation_matrix<T, X> & r_wave) {
        lean_assert(bump_start <= bump_end);
        if (bump_start == bump_end) {
            return;
        }

        r_wave[bump_start] = bump_end; // sending the offensive column to the end of the bump

        for ( unsigned i = bump_start + 1 ; i <= bump_end; i++ ) {
            r_wave[i] = i - 1;
        }

        m_U.multiply_from_right(r_wave);
        m_U.multiply_from_left_with_reverse(r_wave);
    }

    void scan_last_row_to_work_vector(unsigned lowest_row_of_the_bump) {
        std::vector<indexed_value<T>> & last_row_vec = m_U.get_row_values(m_U.adjust_row(lowest_row_of_the_bump));
        for (auto & iv : last_row_vec) {
            if (is_zero(iv.m_value)) continue;
            lean_assert(!m_settings.abs_val_is_smaller_than_drop_tolerance(iv.m_value));
            unsigned adjusted_col = m_U.adjust_column_inverse(iv.m_index);
            if (adjusted_col < lowest_row_of_the_bump) {
                m_row_eta_work_vector.set_value(-iv.m_value, adjusted_col);
            } else  {
                m_row_eta_work_vector.set_value(iv.m_value, adjusted_col); // preparing to calculate the real value in the matrix
            }
        }
    }

    bool diagonal_element_is_off(T diag_element) {
        return false;
    }

    void pivot_and_solve_the_system(unsigned replaced_column, unsigned lowest_row_of_the_bump) {
        // we have the system right side at m_row_eta_work_vector now
        // solve the system column wise
        for (unsigned j = replaced_column; j < lowest_row_of_the_bump; j++) {
            T v = m_row_eta_work_vector[j];
            if (numeric_traits<T>::is_zero(v)) continue; // this column does not contribute to the solution
            unsigned aj = m_U.adjust_row(j);
            std::vector<indexed_value<T>> & row = m_U.get_row_values(aj);
            for (auto & iv : row) {
                unsigned col = m_U.adjust_column_inverse(iv.m_index);
                lean_assert(col >= j || numeric_traits<T>::is_zero(iv.m_value));
                if (col == j) continue;
                if (numeric_traits<T>::is_zero(iv.m_value)) {
                    continue;
                }
                // the -v is for solving the system ( to zero the last row), and +v is for pivoting
                T delta = col < lowest_row_of_the_bump? -v * iv.m_value: v * iv.m_value;
                lean_assert(numeric_traits<T>::is_zero(delta) == false);

                if (numeric_traits<T>::is_zero(m_row_eta_work_vector[col])) {
                    if (!m_settings.abs_val_is_smaller_than_drop_tolerance(delta)){
                        m_row_eta_work_vector.set_value(delta, col);
                    }
                } else {
                    T t = (m_row_eta_work_vector[col] += delta);
                    if (m_settings.abs_val_is_smaller_than_drop_tolerance(t)){
                        m_row_eta_work_vector[col] = numeric_traits<T>::zero();
                        auto it = std::find(m_row_eta_work_vector.m_index.begin(), m_row_eta_work_vector.m_index.end(), col);
                        if (it != m_row_eta_work_vector.m_index.end())
                            m_row_eta_work_vector.m_index.erase(it);
                    }
                }
            }
        }
        lean_assert(m_row_eta_work_vector.is_OK());
    }
    // see Achim Koberstein's thesis page 58, but here we solve the system and pivot to the last
    // row at the same time
    row_eta_matrix<T, X> *get_row_eta_matrix_and_set_row_vector(unsigned replaced_column, unsigned lowest_row_of_the_bump, const T &  pivot_elem_for_checking) {
        if (replaced_column == lowest_row_of_the_bump) return nullptr;
        scan_last_row_to_work_vector(lowest_row_of_the_bump);
        pivot_and_solve_the_system(replaced_column, lowest_row_of_the_bump);
        T denom = std::max(T(1), abs(pivot_elem_for_checking));
        if (
#ifdef LEAN_DEBUG
            !is_zero(pivot_elem_for_checking) &&
#endif
            !m_settings.abs_val_is_smaller_than_pivot_tolerance((m_row_eta_work_vector[lowest_row_of_the_bump] - pivot_elem_for_checking) / denom)) {
            //            std::cout << "m_row_eta_work_vector[" << lowest_row_of_the_bump << "] = " << T_to_string(m_row_eta_work_vector[lowest_row_of_the_bump]) << ", but pivot = " << T_to_string(pivot_elem_for_checking) << endl;
            set_status(LU_status::Degenerated);
            //            std::cout << "diagonal element is off" << endl;
            return nullptr;
        }
#ifdef LEAN_DEBUG
        auto ret = new row_eta_matrix<T, X>(replaced_column, lowest_row_of_the_bump, m_dim);
#else
        auto ret = new row_eta_matrix<T, X>(replaced_column, lowest_row_of_the_bump);
#endif

        for (auto j : m_row_eta_work_vector.m_index) {
            if (j < lowest_row_of_the_bump) {
                auto & v = m_row_eta_work_vector[j];
                if (!is_zero(v)) {
                    if (!m_settings.abs_val_is_smaller_than_drop_tolerance(v)){
                        ret->push_back(j, v);
                    }
                    v = numeric_traits<T>::zero();
                }
            }
        } // now the lowest_row_of_the_bump contains the rest of the row to the right of the bump with correct values
        return ret;
    }

    // This method does not update the basis: is_correct() should not be called since it works with the basis.
    void replace_column(unsigned leaving, T pivot_elem, indexed_vector<T> & w){
        lean_assert(m_basis_heading[leaving] >= 0);
        unsigned replaced_column =  transform_U_to_V_by_replacing_column(leaving, w);
        unsigned lowest_row_of_the_bump = m_U.lowest_row_in_column(replaced_column);
        permutation_matrix<T, X> r_wave(m_dim);
        calculate_r_wave_and_update_U(replaced_column, lowest_row_of_the_bump, r_wave);
        auto row_eta = get_row_eta_matrix_and_set_row_vector(replaced_column, lowest_row_of_the_bump, pivot_elem);
        if (get_status() == LU_status::Degenerated) {
            m_row_eta_work_vector.clear_all();
            return;
        }
        m_Q.multiply_by_permutation_from_right(r_wave);
        m_R.multiply_by_permutation_reverse_from_left(r_wave);
        if (row_eta != nullptr) {
            row_eta->conjugate_by_permutation(m_Q);
            push_matrix_to_tail(row_eta);
        }
        calculate_Lwave_Pwave_for_bump(replaced_column, lowest_row_of_the_bump);
        lean_assert(m_U.is_upper_triangular_and_maximums_are_set_correctly_in_rows(m_settings));
        lean_assert(w.is_OK() && m_row_eta_work_vector.is_OK());
    }

    void calculate_Lwave_Pwave_for_bump(unsigned replaced_column, unsigned lowest_row_of_the_bump){
        T diagonal_elem;
        if (replaced_column < lowest_row_of_the_bump) {
            diagonal_elem = m_row_eta_work_vector[lowest_row_of_the_bump];
            //          lean_assert(m_row_eta_work_vector.is_OK());
            m_U.set_row_from_work_vector_and_clean_work_vector_not_adjusted(m_U.adjust_row(lowest_row_of_the_bump), m_row_eta_work_vector, m_settings);
        } else {
            diagonal_elem = m_U(lowest_row_of_the_bump, lowest_row_of_the_bump); // todo - get it more efficiently
        }
        if (m_settings.abs_val_is_smaller_than_pivot_tolerance(diagonal_elem)) {
            set_status(LU_status::Degenerated);
            return;
        }

        calculate_Lwave_Pwave_for_last_row(lowest_row_of_the_bump, diagonal_elem);
        //         lean_assert(m_U.is_upper_triangular_and_maximums_are_set_correctly_in_rows(m_settings));
    }

    void calculate_Lwave_Pwave_for_last_row(unsigned lowest_row_of_the_bump, T diagonal_element) {
        auto l = new one_elem_on_diag<T, X>(lowest_row_of_the_bump, diagonal_element);
#ifdef LEAN_DEBUG
        l->set_number_of_columns(m_dim);
#endif
        push_matrix_to_tail(l);
        m_U.divide_row_by_constant(lowest_row_of_the_bump, diagonal_element, m_settings);
        l->conjugate_by_permutation(m_Q);
    }

    void prepare_entering(unsigned entering, indexed_vector<T> & w) {
        init_vector_w(entering, w);
    }
}; // end of lu
template <typename T, typename X>
void init_factorization(lu<T, X>* & factorization, static_matrix<T, X> & m_A, std::vector<unsigned> & m_basis, std::vector<int> & m_basis_heading, lp_settings &m_settings, std::vector<unsigned> & non_basic_columns) {
    if (factorization != nullptr) {
        delete factorization;
    }
    factorization = new lu<T, X>(m_A, m_basis, m_basis_heading, m_settings, non_basic_columns);
    if (factorization->get_status() != LU_status::OK) {
        std::cout << "failing in init_factorization" << std::endl;
        return;
    }
}

#ifdef LEAN_DEBUG
template <typename T, typename X>
dense_matrix<T, X>  get_B(lu<T, X>& f) {
    dense_matrix<T, X>  B(f.dimension(), f.dimension());
    for (unsigned i = 0; i < f.dimension(); i++)
        for (unsigned j = 0; j < f.dimension(); j++)
            B.set_elem(i, j, f.B_(i, j));

    return B;
}
#endif
}
