/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/numerics/float.h"
#include "util/lp/permutation_matrix.h"
#include <unordered_map>
#include "util/lp/static_matrix.h"
#include <set>
#include <utility>
#include <string>
#include <algorithm>
#include <queue>
#include "util/lp/indexed_value.h"
#include "util/lp/indexed_vector.h"
#include <functional>
#include "util/lp/lp_settings.h"
#include "util/lp/eta_matrix.h"
#include "util/lp/binary_heap_upair_queue.h"
namespace lean {

using std::vector;
using std::cout;
    // it is a square matrix
template <typename T, typename X>
class sparse_matrix
#ifndef NDEBUG
    : public matrix<T, X>
#endif
{
    struct col_header {
        unsigned m_shortened_markovitz = 0;
        vector<indexed_value<T>> m_values; // the actual column values

        col_header()  {}

        void shorten_markovich_by_one() {
            m_shortened_markovitz++;
        }

        void zero_shortened_markovitz() {
            m_shortened_markovitz = 0;
        }
    };

    binary_heap_upair_queue<unsigned> m_pivot_queue;
public:
    vector<vector<indexed_value<T>>>  m_rows;
    vector<col_header> m_columns;
    permutation_matrix<T, X>  m_row_permutation;
    permutation_matrix<T, X>  m_column_permutation;
    indexed_vector<T> m_work_pivot_vector;
#ifndef NDEBUG
    // dense_matrix<T> m_dense;
#endif
    /*
      the rule is: row i is mapped to m_row_permutation[i] and
      column j is mapped to m_column_permutation.apply_reverse(j)
    */

    unsigned adjust_row(unsigned row)  const{
        return m_row_permutation[row];
    }

    unsigned adjust_column(unsigned  col)  const{
        return m_column_permutation.apply_reverse(col);
    }

    unsigned adjust_row_inverse(unsigned row)  const{
        return m_row_permutation.apply_reverse(row);
    }

    unsigned adjust_column_inverse(unsigned  col)  const{
        return m_column_permutation[col];
    }

    void copy_column_from_static_matrix(unsigned col, static_matrix<T, X> const &A, unsigned col_index_in_the_new_matrix) {
        vector<column_cell<T>> const & A_col_vector = A.m_columns[col];
        unsigned size = A_col_vector.size();
        vector<indexed_value<T>> & new_column_vector = m_columns[col_index_in_the_new_matrix].m_values;
        for (unsigned l = 0; l < size; l++) {
            column_cell<T> const & col_cell = A_col_vector[l];
            unsigned col_offset = new_column_vector.size();
            vector<indexed_value<T>> & row_vector = m_rows[col_cell.m_i];
            unsigned row_offset = row_vector.size();
            new_column_vector.push_back(indexed_value<T>(col_cell.m_value, col_cell.m_i, row_offset));
            row_vector.push_back(indexed_value<T>(col_cell.m_value, col_index_in_the_new_matrix, col_offset));
        }
    }

    void copy_B(static_matrix<T, X> const &A, std::vector<unsigned> & basis) {
        unsigned m = A.row_count(); // this should be the size of basis
        for (unsigned j = m; j-- > 0;) {
            copy_column_from_static_matrix(basis[j], A, j);
        }
    }

public:
    // constructor that copies columns of the basis from A
    sparse_matrix(static_matrix<T, X> const &A, std::vector<unsigned> & basis) :
        m_pivot_queue(A.row_count()),
        m_row_permutation(A.row_count()),
        m_column_permutation(A.row_count()),
        m_work_pivot_vector(A.row_count()) {
        init_row_headers();
        init_column_headers();
        copy_B(A, basis);
    }

    // helper access definitions for debugging region

    class ref_matrix_element {
        sparse_matrix & m_matrix;
        unsigned m_row;
        unsigned m_col;
    public:
        ref_matrix_element(sparse_matrix & m, unsigned row, unsigned col):m_matrix(m), m_row(row), m_col(col) {}
        ref_matrix_element & operator=(T const & v) { m_matrix.set( m_row, m_col, v); return *this; }
        ref_matrix_element & operator=(ref_matrix_element const & v) { m_matrix.set(m_row, m_col, v.m_matrix.get(v.m_row, v.m_col)); return *this; }
        operator T () const { return m_matrix.get(m_row, m_col); }
    };

    class ref_row {
        sparse_matrix & m_matrix;
        unsigned        m_row;
    public:
        ref_row(sparse_matrix & m, unsigned row) : m_matrix(m), m_row(row) {}
        ref_matrix_element operator[](unsigned col) const { return ref_matrix_element(m_matrix, m_row, col); }
    };

    void set_with_no_adjusting_for_row(unsigned row, unsigned col, T val) { // should not be used in efficient code
        vector<indexed_value<T>> & row_vec = m_rows[row];
        for (auto & iv : row_vec) {
            if (iv.m_index == col) {
                iv.set_value(val);
                return;
            }
        }
        // have not found the column between the indices
        row_vec.push_back(indexed_value<T>(val, col)); // what about m_other ???
    }

    void set_with_no_adjusting_for_col(unsigned row, unsigned col, T val) { // should not be used in efficient code
        vector<indexed_value<T>> & col_vec = m_columns[col].m_values;
        for (auto & iv : col_vec) {
            if (iv.m_index == row) {
                iv.set_value(val);
                return;
            }
        }
        // have not found the column between the indices
        col_vec.push_back(indexed_value<T>(val, row)); // what about m_other ???
    }


    void set_with_no_adjusting(unsigned row, unsigned col, T val) { // should not be used in efficient code
        set_with_no_adjusting_for_row(row, col, val);
        set_with_no_adjusting_for_col(row, col, val);
    }

    void set(unsigned row, unsigned col, T val) { // should not be used in efficient code
        lean_assert(row < dimension() && col < dimension());
        //            m_dense.set_elem(row, col, val);
        row = adjust_row(row);
        col = adjust_column(col);
        set_with_no_adjusting(row, col, val);
        //            lean_assert(*this == m_dense);
    }

    T const & get_not_adjusted(unsigned row, unsigned col) const {
        for (indexed_value<T> const & iv : m_rows[row]) {
            if (iv.m_index == col) {
                return iv.m_value;
            }
        }
        return numeric_traits<T>::zero();
    }

    T const & get(unsigned row, unsigned col) const { // should not be used in efficient code
        row = adjust_row(row);
        auto & row_chunk = m_rows[row];
        col = adjust_column(col);
        for (indexed_value<T> const & iv : row_chunk) {
            if (iv.m_index == col) {
                return iv.m_value;
            }
        }
        return numeric_traits<T>::zero();
    }

    ref_row operator[](unsigned row) { return ref_row(*this, row); }

    ref_matrix_element operator()(unsigned row, unsigned col) { return ref_matrix_element(*this, row, col); }

    T operator() (unsigned row, unsigned col) const { return get(row, col); }

    // starting inner classes

    // end of access for debugging helpers

    vector<indexed_value<T>> & get_row_values(unsigned row) {
        return m_rows[row];
    }

    vector<indexed_value<T>> const & get_row_values(unsigned row) const {
        return m_rows[row];
    }

    vector<indexed_value<T>> & get_column_values(unsigned col) {
        return m_columns[col].m_values;
    }

    vector<indexed_value<T>> const & get_column_values(unsigned col) const {
        return m_columns[col].m_values;
    }

    // constructor creating a zero matrix of dim*dim
    sparse_matrix(unsigned dim) :
        m_pivot_queue(dim), // dim will be the initial size of the queue
        m_row_permutation(dim),
        m_column_permutation(dim),
        m_work_pivot_vector(dim) {
        init_row_headers();
        init_column_headers();
    }



    unsigned dimension() const {return m_row_permutation.size();}

#ifndef NDEBUG
    unsigned row_count() const {return dimension();}
    unsigned column_count() const {return dimension();}
#endif

    void init_row_headers() {
        for (unsigned l = 0; l < m_row_permutation.size(); l++) {
            m_rows.push_back(vector<indexed_value<T>>());
        }
    }

    void init_column_headers() { // do we alway have only a square sparse_matrix?
        for (unsigned l = 0; l < m_row_permutation.size(); l++) {
            m_columns.push_back(col_header());
        }
    }

    unsigned lowest_row_in_column(unsigned j) {
        auto & mc = get_column_values(adjust_column(j));
        unsigned ret = 0;
        for (auto & iv : mc) {
            unsigned row = adjust_row_inverse(iv.m_index);
            if (row > ret) {
                ret = row;
            }
        }
        return ret;
    }

    unsigned number_of_non_zeroes_in_row(unsigned i) const {
        lean_assert(i < dimension());
        return m_rows[i].size();
    }

    unsigned number_of_non_zeroes_in_column(unsigned i) const {
        lean_assert(i < dimension());
        return m_columns[i].m_values.size();
    }



    indexed_value<T> & column_iv_other(indexed_value<T> & iv) {
        return m_rows[iv.m_index][iv.m_other];
    }

    indexed_value<T> & row_iv_other(indexed_value<T> & iv) {
        lean_assert(m_columns[iv.m_index].m_values.size() > iv.m_other);
        return m_columns[iv.m_index].m_values[iv.m_other];
    }


    void remove_element(vector<indexed_value<T>> & row_vals, unsigned row_offset, vector<indexed_value<T>> & column_vals, unsigned column_offset) {
        if (column_offset != column_vals.size() - 1) {
            auto & column_iv = column_vals[column_offset] = column_vals.back(); // copy from the tail
            column_iv_other(column_iv).m_other = column_offset;
            if (row_offset != row_vals.size() - 1) {
                auto & row_iv = row_vals[row_offset] = row_vals.back(); // copy from the tail
                row_iv_other(row_iv).m_other = row_offset;
            }
        } else if (row_offset != row_vals.size() - 1) {
            auto & row_iv = row_vals[row_offset] = row_vals.back(); // copy from the tail
            row_iv_other(row_iv).m_other = row_offset;
        }
        // do nothing - just decrease the sizes
        column_vals.pop_back();
        row_vals.pop_back();
    }

    void remove_element(vector<indexed_value<T>> & row_chunk, indexed_value<T> & row_el_iv) {
        auto & column_chunk = get_column_values(row_el_iv.m_index);
        indexed_value<T> & col_el_iv = column_chunk[row_el_iv.m_other];
        remove_element(row_chunk, col_el_iv.m_other, column_chunk, row_el_iv.m_other);
    }

    void put_max_index_to_0(vector<indexed_value<T>> & row_vals, unsigned max_index)  {
        if (max_index == 0) return;
        indexed_value<T> * max_iv = & row_vals[max_index];
        indexed_value<T> * start_iv = & row_vals[0];
        // update the "other" columns elements which are bound to the start_iv and max_iv
        m_columns[max_iv->m_index].m_values[max_iv->m_other].m_other = 0;
        m_columns[start_iv->m_index].m_values[start_iv->m_other].m_other = max_index;

        // swap the elements
        indexed_value<T> t = * max_iv;
        * max_iv = * start_iv;
        * start_iv = t;
    }

    void set_max_in_row(unsigned row) {
        set_max_in_row(m_rows[row]);
    }

    void set_max_in_row(vector<indexed_value<T>> & row_vals) {
        if (row_vals.size() == 0)
            return;
        T max_val = numeric_traits<T>::zero();
        int max_index = 0;
        for (unsigned i = row_vals.size(); i-- > 0;) {
            T iabs = abs(row_vals[i].m_value);
            if (iabs > max_val) {
                max_val = iabs;
                max_index = i;
            }
        }
        put_max_index_to_0(row_vals, max_index);
    }

    bool pivot_with_eta(unsigned i, eta_matrix<T, X> *eta_matrix, lp_settings & settings) {
        T pivot = eta_matrix->get_diagonal_element();
        for (auto it = eta_matrix->get_sparse_vector_iterator(); !it.done(); it.move()) {
            if (!pivot_row_to_row(i, it.value(), it.index(), settings))
                return false;
        }
        divide_row_by_constant(i, pivot, settings);
        if (!shorten_active_matrix(i, eta_matrix)) {
            return false;
        }

        return true;
    }

    void scan_row_to_work_vector(unsigned row, unsigned pivot_column) {
        for (auto & iv : m_rows[row]) {
            if (iv.m_index != pivot_column) {
                m_work_pivot_vector.set_value(iv.m_value, iv.m_index);
            }
        }
    }

    // This method pivots row i to row i0 by muliplying row i by
    // alpha and adding it to row i0.
    // After pivoting the row i0 has a max abs value set correctly at the beginning of m_start,
    // Returns false if the resulting row is all zeroes, and true otherwise
    bool pivot_row_to_row(unsigned i, T alpha, unsigned i0, lp_settings & settings ) {
        lean_assert(i < dimension() && i0 < dimension());
        lean_assert(i != i0);
        unsigned pivot_col = adjust_column(i);
        i = adjust_row(i);
        i0 = adjust_row(i0);
        scan_row_to_work_vector(i0, pivot_col);

        auto & row_vals = m_rows[i];
        //        lean_assert(row_vals.size() > 0);
        for (auto & iv : row_vals) {
            unsigned j = iv.m_index;
            if (j == pivot_col) continue;
            T work_array_at_j = m_work_pivot_vector[j];
            if (numeric_traits<T>::is_zero(work_array_at_j)) {
                T val = alpha * iv.m_value;
                if (settings.abs_val_is_smaller_than_drop_tolerance(val)) {
                    continue;
                }
                m_work_pivot_vector.set_value(val, j);
            } else { // the index is already inside
                //     lean_assert(std::find(m_work_pivot_vector.m_index.begin(),
                //                    m_work_pivot_vector.m_index.end(), j) != m_work_pivot_vector.m_index.end());
                T val = alpha * iv.m_value + work_array_at_j;
                if (settings.abs_val_is_smaller_than_drop_tolerance(val)) {
                    m_work_pivot_vector[j] = numeric_traits<T>::zero();
                } else {
                    m_work_pivot_vector[j] = val;
                }
            }
        }

#ifndef NDEBUG
        lean_assert(numeric_traits<T>::is_zero(m_work_pivot_vector[pivot_col]));
#endif
        if (!set_row_from_work_vector_and_clean_work_vector(i0)) {
            return false;
        }
        return true;
    }

    // set the max val as well
    // returns false if the resulting row is all zeroes, and true otherwise
    bool set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned i0, indexed_vector<T> & work_vec,
                                                                     lp_settings & settings) {
        remove_zero_elements_and_set_data_on_existing_elements_not_adjusted(i0, work_vec, settings);
        // all non-zero elements in m_work_pivot_vector are new
        for (unsigned j : work_vec.m_index) {
            if (numeric_traits<T>::is_zero(work_vec[j])) {
                continue;
            }
            lean_assert(!settings.abs_val_is_smaller_than_drop_tolerance(work_vec[j]));
            add_new_element(i0, adjust_column(j), work_vec[j]);
            work_vec[j] = numeric_traits<T>::zero();
        }
        work_vec.m_index.clear();
        auto & row_vals = m_rows[i0];
        if (row_vals.size() == 0) {
            return false;
        }
        set_max_in_row(row_vals);  // it helps to find larger pivots
        return true;
    }


    // set the max val as well
    // returns false if the resulting row is all zeroes, and true otherwise
    bool set_row_from_work_vector_and_clean_work_vector(unsigned i0) {
        remove_zero_elements_and_set_data_on_existing_elements(i0);
        // all non-zero elements in m_work_pivot_vector are new
        for (unsigned j : m_work_pivot_vector.m_index) {
            if (numeric_traits<T>::is_zero(m_work_pivot_vector[j])) {
                continue;
            }
            add_new_element(i0, j, m_work_pivot_vector[j]);
            m_work_pivot_vector[j] = numeric_traits<T>::zero();
        }
        m_work_pivot_vector.m_index.clear();
        auto & row_vals = m_rows[i0];
        if (row_vals.size() == 0) {
            return false;
        }
        set_max_in_row(row_vals);  // it helps to find larger pivots
        return true;
    }

    void remove_zero_elements_and_set_data_on_existing_elements(unsigned row) {
        auto & row_vals = m_rows[row];
        for (unsigned k = row_vals.size(); k-- > 0;) { // we cannot simply run the iterator since we are removing
            // elements from row_vals
            auto & row_el_iv = row_vals[k];
            unsigned j = row_el_iv.m_index;
            if (is_zero(m_work_pivot_vector[j])) {
                remove_element(row_vals, row_el_iv);
            } else {
                m_columns[j].m_values[row_el_iv.m_other].set_value(m_work_pivot_vector[j]);
                row_el_iv.set_value(m_work_pivot_vector[j]);
                m_work_pivot_vector[j] = zero_of_type<T>();
            }
        }
    }

    // work_vec here has not adjusted column indices
    void remove_zero_elements_and_set_data_on_existing_elements_not_adjusted(unsigned row, indexed_vector<T> & work_vec, lp_settings & settings) {
        auto & row_vals = m_rows[row];
        for (unsigned k = row_vals.size(); k-- > 0;) { // we cannot simply run the iterator since we are removing
            // elements from row_vals
            auto & row_el_iv = row_vals[k];
            unsigned j = row_el_iv.m_index;
            unsigned rj = adjust_column_inverse(j);
            T val = work_vec[rj];
            if (settings.abs_val_is_smaller_than_drop_tolerance(val)) {
                remove_element(row_vals, row_el_iv);
                lean_assert(numeric_traits<T>::is_zero(val));
            } else {
                m_columns[j].m_values[row_el_iv.m_other].set_value(row_el_iv.m_value = val);
                work_vec[rj] = numeric_traits<T>::zero();
            }
        }
    }


    void multiply_from_right(permutation_matrix<T, X>& p) {
        //            m_dense = m_dense * p;
        m_column_permutation.multiply_by_permutation_from_right(p);
        //            lean_assert(*this == m_dense);
    }

    void multiply_from_left(permutation_matrix<T, X>& p) {
        //            m_dense = p * m_dense;
        m_row_permutation.multiply_by_permutation_from_left(p);
        //            lean_assert(*this == m_dense);
    }

    void multiply_from_left_with_reverse(permutation_matrix<T, X>& p) {
        //            m_dense = p * m_dense;
        m_row_permutation.multiply_by_permutation_reverse_from_left(p);
        //            lean_assert(*this == m_dense);
    }

    // adding delta columns at the end of the matrix
    void add_columns_at_the_end(unsigned delta) {
        for (unsigned i = 0; i < delta; i++) {
            col_header col_head;
            m_columns.push_back(col_head);
        }
        m_column_permutation.enlarge(delta);
    }

    void delete_column(int i) {
        lean_assert(i < dimension());
        for (auto cell = m_columns[i].m_head; cell != nullptr;) {
            auto next_cell = cell->m_down;
            kill_cell(cell);
            cell = next_cell;
        }
    }

    bool is_a_unit_matrix() {
        for (int i = 0; i < m_rows.size(); i++) {
            auto * cell = m_rows[i]->m_head;
            if (cell == nullptr || cell->m_j != i || cell->m_value != 1 || cell->m_right != nullptr) {
                return false;
            }
        }
        return true;
    }

    void swap_columns(unsigned a, unsigned b) {
       // cout << "swaapoiiin" << endl;
       // dense_matrix<T, X> d(*this);
        m_column_permutation.transpose_from_left(a, b);
       // d.swap_columns(a, b);
       // lean_assert(*this == d);
    }

    void swap_rows(unsigned a, unsigned b) {
        m_row_permutation.transpose_from_right(a, b);
        //            m_dense.swap_rows(a, b);
        //            lean_assert(*this == m_dense);
    }

    void divide_row_by_constant(unsigned i, T & t, lp_settings & settings) {
        lean_assert(!settings.abs_val_is_smaller_than_zero_tolerance(t));
        i = adjust_row(i);
        for (auto & iv : m_rows[i]) {
            T v = iv.m_value / t;
            if (settings.abs_val_is_smaller_than_drop_tolerance(v)){
                 v = numeric_traits<T>::zero();
            }
            m_columns[iv.m_index].m_values[iv.m_other].set_value(iv.m_value = v);
        }
    }

    T dot_product_with_column(T const * y, unsigned j) {
        lean_assert(j < dimension());
        T ret = numeric_traits<T>::zero();
        auto & mc = m_columns[adjust_column(j)].m_chunk;
        for (int i = mc.m_length - 1; i >= 0; i--) {
            auto & iv = mc.m_start[i];
            ret += y[m_row_permutation.apply_reverse(iv.m_index)] * iv.m_value;
        }
        return ret;
    }

    bool close(T a, T b) {
        return // (numeric_traits<T>::precise() && numeric_traits<T>::is_zero(a - b))
            // ||
            fabs(numeric_traits<T>::get_double(a - b)) < 0.0000001;
    }

    // solving x * this = y, and putting the answer into y
    // the matrix here has to be upper triangular
    void solve_y_U(std::vector<T> & y) const { // works by rows
#ifndef NDEBUG
        // T * rs = clone_vector<T>(y, dimension());
#endif
        unsigned end = dimension() - 1;
        for (unsigned i = 0; i < end; i++) {
            // all y[i] has correct values already
            const T & yv = y[i];
            if (numeric_traits<T>::is_zero(yv)) continue;
            auto & mc = get_row_values(adjust_row(i));
            for (auto & c : mc) {
                unsigned col = adjust_column_inverse(c.m_index);
                if (col != i) {
                    y[col] -= c.m_value * yv;
                }
            }
        }
#ifndef NDEBUG
        // dense_matrix<T> deb(*this);
        // T * clone_y = clone_vector<T>(y, dimension());
        // deb.apply_from_right(clone_y);
        // lean_assert(vectors_are_equal(rs, clone_y, dimension()));
        // delete [] clone_y;
        // delete [] rs;
#endif
    }

    // fills the indices for such that y[i] can be not a zero
    // sort them so the smaller indices come first
    void fill_reachable_indices(std::set<unsigned> & rset, T *y) {
        // std::queue<unsigned> q;
        // int m = dimension();
        // for (int i = m - 1; i >= 0; i--) {
        //     if (!numeric_traits<T>::is_zero(y[i])){
        //         for (cell * c = m_columns[adjust_column(i)].m_head; c != nullptr; c = c->m_down) {
        //             unsigned row = adjust_row_inverse(c->m_i);
        //             q.push(row);
        //         }
        //     }
        // }
        // while (!q.empty()) {
        //     unsigned i = q.front();
        //     q.pop();
        //     for (cell * c = m_columns[adjust_column(i)].m_head; c != nullptr; c = c->m_down) {
        //         unsigned row = adjust_row_inverse(c->m_i);
        //         if (rset.find(row) == rset.end()){
        //             rset.insert(row);
        //             q.push(row);
        //         }
        //     }
        //     }
    }

    // solving this * x = y, and putting the answer into y
    // the matrix here has to be upper triangular
    void solve_U_y_(T * y) {  // the row wise version
#ifndef NDEBUG
        // T * rs = clone_vector<T>(y, dimension());
#endif
        lean_assert(dimension() == dimension());
        for (int i = dimension() - 2 ; i >= 0; i--) {
            auto & mc = get_row_values(adjust_row(i));
            for (auto & c : mc) {
                unsigned col = m_column_permutation[c.m_index];
                lean_assert(col > i || (col  == i && close(c.m_value, numeric_traits<T>::one())));
                if (col == i) {
                    continue;
                }
                y[i] -= y[col] * c.m_value;
            }
        }
#ifndef NDEBUG
        // dense_matrix<T> deb(*this);
        // T * clone_y = clone_vector<T>(y, dimension());
        // deb.apply_from_left(clone_y);
        // lean_assert(vectors_are_equal(rs, clone_y, dimension()));
        // delete [] rs;
        // delete [] clone_y;
#endif
    }
    // solving this * x = y, and putting the answer into y
    // the matrix here has to be upper triangular
    void solve_U_y(T * y) { // the columns have to be correct - it is a column wise version
#ifndef NDEBUG
        // T * rs = clone_vector<T>(y, dimension());
#endif
        for (unsigned j = dimension() - 1; j > 0; j--) {
            T yj = y[j];
            if (numeric_traits<T>::is_zero(yj)) continue;
            auto & mc = m_columns[adjust_column(j)].m_values;
            for (auto & iv : mc) {
                unsigned i = adjust_row_inverse(iv.m_index);
                if (i != j) {
                    y[i] -= iv.m_value * yj;
                }
            }
        }
#ifndef NDEBUG
        // dense_matrix<T> deb(*this);
        // T * clone_y = clone_vector<T>(y, dimension());
        // deb.apply_from_left(clone_y);
        // lean_assert(vectors_are_equal(rs, clone_y, dimension()));
#endif
    }

    template <typename L>
        void find_error_in_solution_U_y(vector<L>& y_orig, vector<L> & y) {
        unsigned i = dimension();
        while (i--) {
            y_orig[i] -= dot_product_with_row(i, y);
        }
    }

    template <typename L>
    void add_delta_to_solution(const vector<L>& del, vector<L> & y) {
        unsigned i = dimension();
        while (i--) {
            y[i] += del[i];
        }
    }

    template <typename L>
    void double_solve_U_y(vector<L>& y){
        vector<L> y_orig(y); // copy y aside
        solve_U_y(y);
        find_error_in_solution_U_y(y_orig, y);
        // y_orig contains the error now
        solve_U_y(y_orig);
        add_delta_to_solution(y_orig, y);
    }
    // solving this * x = y, and putting the answer into y
    // the matrix here has to be upper triangular
    template <typename L>
    void solve_U_y(std::vector<L> & y) { // it is a column wise version
#ifndef NDEBUG
        // T * rs = clone_vector<T>(y, dimension());
#endif

        for (unsigned j = dimension(); j--; ) {
            const L & yj = y[j];
            if (is_zero(yj)) continue;
            auto & mc = m_columns[adjust_column(j)].m_values;
            for (auto & iv : mc) {
                unsigned i = adjust_row_inverse(iv.m_index);
                if (i != j) {
                    y[i] -= iv.m_value * yj;
                }
            }
        }
#ifndef NDEBUG
        // dense_matrix<T> deb(*this);
        // T * clone_y = clone_vector<T>(y, dimension());
        // deb.apply_from_left(clone_y);
        // lean_assert(vectors_are_equal(rs, clone_y, dimension()));
#endif
    }

#ifndef NDEBUG
    T get_elem(unsigned i, unsigned j) const { return get(i, j); }
    unsigned get_number_of_rows() const { return dimension(); }
    unsigned get_number_of_columns() const { return dimension(); }
    virtual void set_number_of_rows(unsigned /*m*/) { }
    virtual void set_number_of_columns(unsigned /*n*/) { }
#endif
    template <typename L>
        L dot_product_with_row (unsigned row, const vector<L> & y) const {
        L ret = zero_of_type<L>();
        auto & mc = get_row_values(adjust_row(row));
        for (auto & c : mc) {
            unsigned col = m_column_permutation[c.m_index];
            ret += c.m_value * y[col];
        }
        return ret;
    }

    unsigned get_number_of_nonzeroes() const {
        unsigned ret = 0;
        for (unsigned i = dimension(); i--; ) {
            ret += number_of_non_zeroes_in_row(i);
        }
        return ret;
    }

    unsigned get_number_of_nonzeroes_below_row(unsigned row) const {
        unsigned ret = 0;
        for (unsigned i = dimension() - 1;
             static_cast<int>(i) >= static_cast<int>(row); i--) {
            ret += number_of_non_zeroes_in_row(adjust_row(i));
        }
        return ret;
    }

    bool get_non_zero_column_in_row(unsigned i, unsigned *j) const {
        // go over the i-th row
        auto & mc = get_row_values(adjust_row(i));
        if (mc.size() > 0) {
            *j = m_column_permutation[mc[0].m_index];
            return true;
        }
        return false;
    }

    void remove_element_that_is_not_in_w(vector<indexed_value<T>> & column_vals, indexed_value<T> & col_el_iv) {
        auto & row_chunk = m_rows[col_el_iv.m_index];
        indexed_value<T> & row_el_iv = row_chunk[col_el_iv.m_other];
        unsigned index_in_row = col_el_iv.m_other;
        remove_element(row_chunk, col_el_iv.m_other, column_vals, row_el_iv.m_other);
        if (index_in_row == 0)
            set_max_in_row(row_chunk);
    }


    // w contains the new column
    // the old column inside of the matrix has not been changed yet
    void remove_elements_that_are_not_in_w_and_update_common_elements(unsigned column_to_replace, indexed_vector<T> & w) {
        // --------------------------------
        // column_vals represents the old column
        auto & column_vals = m_columns[column_to_replace].m_values;
        for (unsigned k = column_vals.size(); k-- > 0;) {
            indexed_value<T> & col_el_iv = column_vals[k];
            unsigned i = col_el_iv.m_index;
            T w_data_at_i = w[adjust_row_inverse(i)];
            if (numeric_traits<T>::is_zero(w_data_at_i)) {
                remove_element_that_is_not_in_w(column_vals, col_el_iv);
            } else {
                auto& row_chunk = m_rows[i];
                unsigned index_in_row = col_el_iv.m_other;
                if (index_in_row == 0) {
                    bool look_for_max = abs(w_data_at_i) < abs(row_chunk[0].m_value);
                    row_chunk[0].set_value(col_el_iv.m_value = w_data_at_i);
                    if (look_for_max)
                        set_max_in_row(i);
                } else {
                    row_chunk[index_in_row].set_value(col_el_iv.m_value = w_data_at_i);
                    if (abs(w_data_at_i) > abs(row_chunk[0].m_value))
                        put_max_index_to_0(row_chunk, index_in_row);
                }
                w[adjust_row_inverse(i)] = numeric_traits<T>::zero();
            }
        }
    }

    void add_new_element(unsigned row, unsigned col, T val) {
        auto & row_vals = m_rows[row];
        auto & col_vals = m_columns[col].m_values;
        unsigned row_el_offs = row_vals.size();
        unsigned col_el_offs = col_vals.size();
        row_vals.push_back(indexed_value<T>(val, col, col_el_offs));
        col_vals.push_back(indexed_value<T>(val, row, row_el_offs));
    }

    // w contains the "rest" of the new column; all common elements of w and the old column has been zeroed
    // the old column inside of the matrix has not been changed yet
    void add_new_elements_of_w_and_clear_w(unsigned column_to_replace, indexed_vector<T> & w, lp_settings & settings) {
        for (unsigned i : w.m_index) {
            T w_at_i = w[i];
            if (numeric_traits<T>::is_zero(w_at_i)) continue; // was dealt with already
            if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_i)) {
                unsigned ai = adjust_row(i);
                add_new_element(ai, column_to_replace, w_at_i);
                auto & row_chunk = m_rows[ai];
                lean_assert(row_chunk.size() > 0);
                if (abs(w_at_i) > abs(row_chunk[0].m_value))
                    put_max_index_to_0(row_chunk, row_chunk.size() - 1);
            }
            w[i] = numeric_traits<T>::zero();
        }
        w.m_index.clear();
    }

    void replace_column(unsigned column_to_replace, indexed_vector<T> & w, lp_settings &settings) {
        column_to_replace = adjust_column(column_to_replace);
        remove_elements_that_are_not_in_w_and_update_common_elements(column_to_replace, w);
        add_new_elements_of_w_and_clear_w(column_to_replace, w, settings);
    }

    T const & get_max_in_row(unsigned row) const {
        return m_rows[adjust_row(row)][0].m_value;
    }

    T const & get_max_in_row_without_adjusting(unsigned row) const {
        return m_rows[row][0].m_value;
    }


    unsigned pivot_score(unsigned i, unsigned j) {
          // It goes like this (rnz-1)(cnz-1) is the Markovitz number, that is the max number of
            // new non zeroes we can obtain after the pivoting.
            // In addition we will get another cnz - 1 elements in the eta matrix created for this pivot,
            // which gives rnz(cnz-1). For example, is 0 for a column singleton, but not for
            // a row singleton ( which is not a column singleton).

        auto col_header = m_columns[j];

        return get_row_values(i).size() * (col_header.m_values.size() - col_header.m_shortened_markovitz - 1);
    }

    void enqueue_domain_into_pivot_queue() {
        lean_assert(m_pivot_queue.size() == 0);
        for (unsigned i = 0; i < dimension(); i++) {
            auto & rh = m_rows[i];
            unsigned rnz = rh.size();
            for (auto iv : rh) {
                unsigned j = iv.m_index;
                m_pivot_queue.enqueue(i, j, rnz * (m_columns[j].m_values.size() - 1));
            }
        }
    }

    void set_max_in_rows() {
        unsigned i = dimension();
        while (i--)
            set_max_in_row(i);
    }


    void zero_shortened_markovitz_numbers() {
        for (auto & ch : m_columns)
            ch.zero_shortened_markovitz();
    }

    void prepare_for_factorization() {
        zero_shortened_markovitz_numbers();
        set_max_in_rows();
        enqueue_domain_into_pivot_queue();
    }

    void recover_pivot_queue(vector<upair> & rejected_pivots)  {
        for (auto p : rejected_pivots) {
            m_pivot_queue.enqueue(p.first, p.second, pivot_score(p.first, p.second));
        }
    }

    int elem_is_too_small(unsigned i, unsigned j, const T & c_partial_pivoting)  {
        auto & row_chunk = m_rows[i];

        if (j == row_chunk[0].m_index) {
            return 0; // the max element is at the head
        }
        T max = abs(row_chunk[0].m_value);
        for (unsigned k = 1; k < row_chunk.size(); k++) {
            auto &iv = row_chunk[k];
            if (iv.m_index == j)
                return abs(iv.m_value) * c_partial_pivoting < max ? 1: 0;
        }
        return 2;  // the element became zero but it still sits in the active pivots?
        cout << "column " << j << " does not belong to row " << i << endl;
        throw "cannot be here";
    }

    bool remove_row_from_active_pivots_and_shorten_columns(unsigned row) {
        unsigned arow = adjust_row(row);
        for (auto & iv : m_rows[arow]) {
            m_pivot_queue.remove(arow, iv.m_index);
            if (adjust_column_inverse(iv.m_index) <= row)
                continue; // this column will be removed anyway
            auto & col = m_columns[iv.m_index];

            col.shorten_markovich_by_one();
            if (col.m_values.size() <= col.m_shortened_markovitz)
                return false; // got a zero column
        }
        return true;
    }

    void remove_pivot_column(unsigned row) {
        unsigned acol = adjust_column(row);
        for (auto & iv : m_columns[acol].m_values)
            if (adjust_row_inverse(iv.m_index) >= row)
                m_pivot_queue.remove(iv.m_index, acol);
    }

    void update_active_pivots(unsigned row) {
        unsigned arow = adjust_row(row);
        for (auto & iv : m_rows[arow]) {
            col_header & ch = m_columns[iv.m_index];
            int cols = ch.m_values.size() - ch.m_shortened_markovitz - 1;
            lean_assert(cols >= 0);
            for (auto &ivc : ch.m_values) {
                unsigned i = ivc.m_index;
                if (adjust_row_inverse(i) <= row) continue; // the i is not an active row
                m_pivot_queue.enqueue(i, iv.m_index, m_rows[i].size()*cols);
            }
        }
    }

    bool shorten_active_matrix(unsigned row, eta_matrix<T, X> *eta_matrix) {
        if (!remove_row_from_active_pivots_and_shorten_columns(row))
            return false;
        remove_pivot_column(row);
        // need to know the max priority of the queue here
        update_active_pivots(row);
        if (eta_matrix == nullptr) return true;
        // it looks like double work, but the pivot scores have changed for all rows
        // touched by eta_matrix
        for (auto it = eta_matrix->get_sparse_vector_iterator(); !it.done(); it.move()) {
            unsigned row = adjust_row(it.index());
            auto & row_values = m_rows[row];
            unsigned rnz = row_values.size();
            for (auto & iv : row_values) {
                col_header& ch = m_columns[iv.m_index];
                int cnz = ch.m_values.size() - ch.m_shortened_markovitz - 1;
                lean_assert(cnz >= 0);
                m_pivot_queue.enqueue(row, iv.m_index, rnz * cnz);
            }
        }

        return true;
    }

    unsigned pivot_score_without_shortened_counters(unsigned i, unsigned j, unsigned k) {
        auto &cols = m_columns[j].m_values;
        unsigned cnz = cols.size();
        for (auto & iv : cols) {
            if (adjust_row_inverse(iv.m_index) < k)
                 cnz--;
        }
        lean_assert(cnz > 0);
        return m_rows[i].m_values.size() * (cnz - 1);
    }
#ifndef NDEBUG
    bool can_improve_score_for_row(unsigned row, unsigned score, T const & c_partial_pivoting, unsigned k) {
        unsigned arow = adjust_row(row);
        auto & row_vals = m_rows[arow].m_values;
        auto & begin_iv = row_vals[0];
        T row_max = abs(begin_iv.m_value);
        lean_assert(adjust_column_inverse(begin_iv.m_index) >= k);
        if (pivot_score_without_shortened_counters(arow, begin_iv.m_index, k) < score) {
            print_active_matrix(k);
            return true;
        }
        for (unsigned jj = 1; jj < row_vals.size(); jj++) {
            auto & iv = row_vals[jj];
            lean_assert(adjust_column_inverse(iv.m_index) >= k);
            lean_assert(abs(iv.m_value) <= row_max);
            if (c_partial_pivoting * abs(iv.m_value) < row_max) continue;
            if (pivot_score_without_shortened_counters(arow, iv.m_index, k) < score) {
                print_active_matrix(k);
                return true;
            }
        }
        return false;
    }
    bool really_best_pivot(unsigned i, unsigned j, T const & c_partial_pivoting, unsigned k) {
        unsigned queue_pivot_score = pivot_score_without_shortened_counters(i, j, k);
        for (unsigned ii = k; ii < dimension(); ii++) {
            lean_assert(!can_improve_score_for_row(ii, queue_pivot_score, c_partial_pivoting, k));
        }
        return true;
    }
    void print_active_matrix(unsigned k) {
        cout << "active matrix for k = " << k << endl;
        if (k >= dimension()) {
            cout << "empty" << endl;
            return;
        }
        unsigned dim = dimension() - k;
        dense_matrix<T, X> b(dim, dim);
        for (unsigned i = 0; i < dim; i++)
            for (unsigned j = 0; j < dim; j++ )
                b.set_elem(i, j, zero_of_type<T>());
        for (int i = k; i < dimension(); i++) {
            unsigned col = adjust_column(i);
            for (auto &iv : get_column_values(col)) {
                unsigned row = iv.m_index;
                unsigned row_ex = this->adjust_row_inverse(row);
                if (row_ex < k) continue;
                auto v = this->get_not_adjusted(row, col);
                b.set_elem(row_ex - k, i -k, v);
            }
        }
        print_matrix(b);
    }
#endif
    bool pivot_queue_is_correct_for_row(unsigned i, unsigned k) {
        unsigned arow = adjust_row(i);
        for (auto & iv : m_rows[arow].m_values) {
            lean_assert(pivot_score_without_shortened_counters(arow, iv.m_index, k + 1) ==
                m_pivot_queue.get_priority(arow, iv.m_index));
        }
        return true;
    }

    bool pivot_queue_is_correct_after_pivoting(int k) {
        for (unsigned i = k + 1; i < dimension(); i++ )
            lean_assert(pivot_queue_is_correct_for_row(i, k));
        lean_assert(m_pivot_queue.is_correct());
        return true;
    }


    bool get_pivot_for_column(unsigned &i, unsigned &j, T const & c_partial_pivoting, unsigned k) {
        vector<upair> pivots_candidates_that_are_too_small;
        while (!m_pivot_queue.is_empty()) {
            m_pivot_queue.dequeue(i, j);
            unsigned i_inv = adjust_row_inverse(i);
            if (i_inv < k) continue;
            unsigned j_inv = adjust_column_inverse(j);
            if (j_inv < k) continue;
            int small = elem_is_too_small(i, j, c_partial_pivoting);
            if (!small) {
#ifndef NDEBUG
                // if (!really_best_pivot(i, j, c_partial_pivoting, k)) {
                //     print_active_matrix(k);
                //     lean_assert(false);
                //  }
#endif

                recover_pivot_queue(pivots_candidates_that_are_too_small);
                i = i_inv;
                j = j_inv;
                return true;
            }
            if (small != 2) // 2 means that the pair is not in the matrix
                pivots_candidates_that_are_too_small.emplace_back(i, j);
        }
        recover_pivot_queue(pivots_candidates_that_are_too_small);
        return false;
        /*
        unsigned m = dimension();
        unsigned markovitz_number_min = m * m;
        unsigned iterations = 0;
        for (unsigned k = 2; k <= m; k++){
            if (markovitz_number_min < (k-1) * (k-1))
                return true;

            if (get_pivot_in_k_short_columns(k, markovitz_number_min, i, j, c_partial_pivoting, iterations)
                ||
                get_pivot_in_k_short_rows(k, markovitz_number_min, i, j, c_partial_pivoting, iterations)) {
                return true;
            }
            if (iterations > search_depth * 2 &&  markovitz_number_min < m * m)
                return true;
        }
        return  markovitz_number_min < m * m;
        */
    }

    bool elem_is_too_small(vector<indexed_value<T>> & row_chunk, indexed_value<T> & iv, T const & c_partial_pivoting) {
        if (&iv == &row_chunk[0]) {
            return false; // the max element is at the head
        }
        T val = abs(iv.m_value);
        T max = abs(row_chunk[0].m_value);
        return val * c_partial_pivoting < max;
    }

    unsigned number_of_non_zeros_in_row(unsigned row) const {
        return m_rows[row].m_values.size();
    }

    unsigned number_of_non_zeros_in_column(unsigned col) const {
        return m_columns[col].m_values.size();
    }



    bool shorten_columns_by_pivot_row(unsigned i, unsigned pivot_column) {
        vector<indexed_value<T>> & row_chunk = get_row_values(i);

        for (indexed_value<T> & iv : row_chunk) {
            unsigned j = iv.m_index;
            if (j == pivot_column) {
                lean_assert(!col_is_active(j));
                continue;
            }
            m_columns[j].shorten_markovich_by_one();

            if (m_columns[j].m_shortened_markovitz >= get_column_values(j).size()) { // got the zero column under the row!
                return false;
            }
        }
        return true;
    }

    bool col_is_active(unsigned j, unsigned pivot) {
        return adjust_column_inverse(j) > pivot;
    }

    bool row_is_active(unsigned i, unsigned pivot) {
        return adjust_row_inverse(i) > pivot;
    }

    void fill_eta_matrix(unsigned j, eta_matrix<T, X> ** eta) {
        vector<indexed_value<T>> & col_chunk = get_column_values(adjust_column(j));
        bool is_unit = true;
        for (auto & iv : col_chunk) {
            unsigned i = adjust_row_inverse(iv.m_index);
            if (i > j) {
                is_unit = false;
                break;
            }
            if (i == j && iv.m_value != 1) {
                is_unit = false;
                break;
            }
        }

        if (is_unit) {
            *eta = nullptr;
            return;
        }

#ifndef NDEBUG
        *eta = new eta_matrix<T, X>(j, dimension());
#else
        *eta = new eta_matrix<T, X>(j);
#endif
        for (auto & iv : col_chunk) {
            unsigned i = adjust_row_inverse(iv.m_index);
            if (i < j) {
                continue;
            }
            if (i > j) {
                (*eta)->push_back(i, - iv.m_value);
            } else { // i == j
                (*eta)->set_diagonal_element(iv.m_value);
            }
        }
        (*eta)->divide_by_diagonal_element();
    }

    bool is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings & settings) const {
        for (unsigned i = 0; i < dimension(); i++) {
            vector<indexed_value<T>> const & row_chunk = get_row_values(i);
            lean_assert(row_chunk.size());
            T const & max = abs(row_chunk[0].m_value);
            unsigned ai = adjust_row_inverse(i);
            for (auto & iv : row_chunk) {
                lean_assert(abs(iv.m_value) <= max);
                unsigned aj = adjust_column_inverse(iv.m_index);
                if (!(ai <= aj || numeric_traits<T>::is_zero(iv.m_value)))
                    return false;
                if (aj == ai) {
                    if (iv.m_value != 1) {
                        cout << "value at diagonal = " << iv.m_value << endl;
                        return false;
                    }
                }
                if (settings.abs_val_is_smaller_than_drop_tolerance(iv.m_value) && (!is_zero(iv.m_value)))
                    return false;
            }
        }
        return true;
    }

    bool is_upper_triangular_until(unsigned k) const {
        for (unsigned j = 0; j < dimension() && j < k; j++) {
            unsigned aj = adjust_column(j);
            auto & col = get_column_values(aj);
            for (auto & iv : col) {
                unsigned row = adjust_row_inverse(iv.m_index);
                if (row > j)
                    return false;
            }
        }
        return true;
    }



    void check_column_vs_rows(unsigned col) {
        auto & mc = get_column_values(col);
        for (indexed_value<T> & column_iv : mc) {
            indexed_value<T> & row_iv = column_iv_other(column_iv);
            if (row_iv.m_index != col) {
                cout << "m_other in row does not belong to column " << col << ", but to column  " << row_iv.m_index << endl;
                lean_assert(false);
            }

            if (& row_iv_other(row_iv) != &column_iv) {
                cout << "row and col do not point to each other" << endl;
                lean_assert(false);
            }

            if (row_iv.m_value != column_iv.m_value) {
                cout << "the data from col " << col << " for row " << column_iv.m_index << " is different in the column " << endl;
                cout << "in the col it is " << column_iv.m_value << ", but in the row it is " << row_iv.m_value << endl;
                lean_assert(false);
            }
        }
    }

    void check_row_vs_columns(unsigned row) {
        auto & mc = get_row_values(row);
        for (indexed_value<T> & row_iv : mc) {
            indexed_value<T> & column_iv = row_iv_other(row_iv);

            if (column_iv.m_index != row) {
                cout << "col_iv does not point to correct row " << row << " but to " << column_iv.m_index << endl;
                lean_assert(false);
            }

            if (& row_iv != & column_iv_other(column_iv)) {
                cout << "row and col do not point to each other" << endl;
                lean_assert(false);
            }

            if (row_iv.m_value != column_iv.m_value) {
                cout << "the data from col " << column_iv.m_index << " for row " << row << " is different in the column " << endl;
                cout << "in the col it is " << column_iv.m_value << ", but in the row it is " << row_iv.m_value << endl;
                lean_assert(false);
            }
        }
    }

    void check_rows_vs_columns() {
        for (unsigned i = 0; i < dimension(); i++) {
            check_row_vs_columns(i);
        }
    }

    void check_columns_vs_rows() {
        for (unsigned i = 0; i < dimension(); i++) {
            check_column_vs_rows(i);
        }
    }

    void map_domain_to_vector(unordered_map<pair<unsigned, unsigned>, unsigned> & domain, vector<pair<unsigned, unsigned>> & vec) {
        lean_assert(domain.size() == 0 && vec.size() == 0);
        for (unsigned i = 0; i < dimension(); i++) {
            vector<indexed_value<T>> & row = get_row_values(i);
            for (auto & iv : row) {
                unsigned j = iv.m_index;
                unsigned nz = vec.size();
                pair<unsigned, unsigned> p(i, j);
                domain[p] = nz;
                vec.push_back(p);
            }
        }
    }

#ifndef NDEBUG
    void check_matrix() {
        check_rows_vs_columns();
        check_columns_vs_rows();
    }
#endif
};
};
