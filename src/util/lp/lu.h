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
#include "util/lp/dense_matrix.h"
namespace lean {
#ifdef LEAN_DEBUG
template <typename T, typename X> // print the nr x nc submatrix at the top left corner
void print_submatrix(sparse_matrix<T, X> & m, unsigned mr, unsigned nc);

template<typename T, typename X>
void print_matrix(static_matrix<T, X> &m, std::ostream & out);

template <typename T, typename X>
void print_matrix(sparse_matrix<T, X>& m, std::ostream & out);
#endif

template <typename T, typename X>
X dot_product(const std::vector<T> & a, const std::vector<X> & b, unsigned l);

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

    one_elem_on_diag(const one_elem_on_diag & o);

#ifdef LEAN_DEBUG
    unsigned m_m;
    unsigned m_n;
    virtual void set_number_of_rows(unsigned m) { m_m = m; m_n = m; }
    virtual void set_number_of_columns(unsigned n) { m_m = n; m_n = n; }
    T m_one_over_val;

    T get_elem (unsigned i, unsigned j) const;

    unsigned row_count() const { return m_m; } // not defined }
    unsigned column_count() const { return m_m; } // not defined  }
#endif
    void apply_from_left(std::vector<X> & w, lp_settings &) {
        w[m_i] /= m_val;
    }

    void apply_from_right(std::vector<T> & w) {
        w[m_i] /= m_val;
    }

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings);

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

enum class LU_status { OK, Degenerated};

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
       std::vector<unsigned> & non_basic_columns);
    void debug_test_of_basis(static_matrix<T, X> const & A, std::vector<unsigned> & basis);


    unsigned non_basic_column_index_in_non_basic_columns(unsigned j) { return - m_basis_heading[j] - 1; }

    void solve_By(std::vector<X> & y);

    void solve_Bd_when_w_is_ready(std::vector<T> & d, indexed_vector<T>& w );

    template <typename L>
    void solve_By_when_y_is_ready(std::vector<L> & y);
    void print_indexed_vector(indexed_vector<T> & w, std::ofstream & f);

    void print_basis(std::ostream & f);
    void print_matrix_compact(std::ostream & f);

    void print(indexed_vector<T> & w);
    void solve_Bd(unsigned a_column, std::vector<T> & d, indexed_vector<T> & w);

    bool column_can_be_taken_to_basis(unsigned i) { return m_basis_heading[i] < 0; }

    void  solve_yB_internal(std::vector<T>& y);

    void add_delta_to_solution(std::vector<T>& yc, std::vector<T>& y);

    void find_error_of_yB(std::vector<T>& yc, const std::vector<T>& y);

    void solve_yB(std::vector<T> & y);

    void apply_Q_R_to_U(permutation_matrix<T, X> & r_wave);

    void change_basis(unsigned entering, unsigned leaving);

    void restore_basis_change(unsigned entering, unsigned leaving);

    LU_status get_status() { return m_status; }

    void set_status(LU_status status) { m_status = status; }

    ~lu();

    T B(unsigned i, unsigned j) { return m_A(i, m_basis[j]); }

    void init_vector_y(std::vector<X> & y);

    void perform_transformations_on_w(indexed_vector<T>& w);

    void init_vector_w(unsigned entering, indexed_vector<T> & w);
    void apply_lp_lists_to_w(indexed_vector<T> & w);
    void apply_lp_lists_to_y(std::vector<X>& y);

    void swap_rows(int j, int k);

    void swap_columns(int j, int pivot_column);

    void push_matrix_to_tail(tail_matrix<T, X>* tm) {
        m_tail.push_back(tm);
    }

    bool pivot_the_row(int row);

    eta_matrix<T, X> * get_eta_matrix_for_pivot(unsigned j);
    // we're processing the column j now
    eta_matrix<T, X> * get_eta_matrix_for_pivot(unsigned j, sparse_matrix<T, X>& copy_of_U);

    void print_basis_heading(std::ostream & out);

    // see page 407 of Chvatal
    unsigned transform_U_to_V_by_replacing_column(unsigned leaving, indexed_vector<T> & w);

#ifdef LEAN_DEBUG
    void check_vector_w(unsigned entering);

    void check_apply_matrix_to_vector(matrix<T, X> *lp, T *w);

    void check_apply_lp_lists_to_w(T * w);

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


    void process_column(int j);

    bool is_correct();

    int basis_heading(unsigned j) {
        lean_assert(j < m_A.column_count());
        return m_basis_heading[j];
    }

#ifdef LEAN_DEBUG
    dense_matrix<T, X> tail_product();
    dense_matrix<T, X>  get_left_side();

    dense_matrix<T, X>  get_right_side();
#endif

    // needed for debugging purposes
    void copy_w(T *buffer, indexed_vector<T> & w);

    // needed for debugging purposes
    void restore_w(T *buffer, indexed_vector<T> & w);
    bool all_columns_and_rows_are_active();

    bool too_dense(unsigned j) const;

    void pivot_in_dense_mode(unsigned i);

    void create_initial_factorization();

    void calculate_r_wave_and_update_U(unsigned bump_start, unsigned bump_end, permutation_matrix<T, X> & r_wave);

    void scan_last_row_to_work_vector(unsigned lowest_row_of_the_bump);

    bool diagonal_element_is_off(T /* diag_element */) { return false; }

    void pivot_and_solve_the_system(unsigned replaced_column, unsigned lowest_row_of_the_bump);
    // see Achim Koberstein's thesis page 58, but here we solve the system and pivot to the last
    // row at the same time
    row_eta_matrix<T, X> *get_row_eta_matrix_and_set_row_vector(unsigned replaced_column, unsigned lowest_row_of_the_bump, const T &  pivot_elem_for_checking);

    // This method does not update the basis: is_correct() should not be called since it works with the basis.
    void replace_column(unsigned leaving, T pivot_elem, indexed_vector<T> & w);

    void calculate_Lwave_Pwave_for_bump(unsigned replaced_column, unsigned lowest_row_of_the_bump);

    void calculate_Lwave_Pwave_for_last_row(unsigned lowest_row_of_the_bump, T diagonal_element);

    void prepare_entering(unsigned entering, indexed_vector<T> & w) {
        init_vector_w(entering, w);
    }
}; // end of lu

template <typename T, typename X>
void init_factorization(lu<T, X>* & factorization, static_matrix<T, X> & m_A, std::vector<unsigned> & m_basis, std::vector<int> & m_basis_heading, lp_settings &m_settings, std::vector<unsigned> & non_basic_columns);

#ifdef LEAN_DEBUG
template <typename T, typename X>
dense_matrix<T, X>  get_B(lu<T, X>& f);
#endif
}
