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
#include "util/lp/sparse_matrix.h"
namespace lean {
template <typename T, typename X>
class square_dense_submatrix : public tail_matrix<T, X> {
    // the submatrix uses the permutations of the parent matrix to access the elements
    struct ref {
        unsigned m_i_offset;
        square_dense_submatrix & m_s;
        ref(unsigned i, square_dense_submatrix & s) :
            m_i_offset((i - s.m_index_start) * s.m_dim), m_s(s){}
        T & operator[] (unsigned j) {
            lean_assert(j >= m_s.m_index_start);
            return m_s.m_v[m_i_offset + m_s.adjust_column(j) - m_s.m_index_start];
        }
        const T & operator[] (unsigned j) const {
            lean_assert(j >= m_s.m_index_start);
            return m_s.m_v[m_i_offset + m_s.adjust_column(j) - m_s.m_index_start];
        }
    };
public: // debug
    unsigned m_index_start;
    unsigned m_dim;
    std::vector<T> m_v;
    sparse_matrix<T, X> * m_parent = nullptr;
    permutation_matrix<T, X>  m_row_permutation;
public:
    permutation_matrix<T, X>  m_column_permutation;
    bool is_active() const { return m_parent != nullptr; }

    square_dense_submatrix() {}

    square_dense_submatrix (sparse_matrix<T, X> *parent_matrix, unsigned index_start);

    void init(sparse_matrix<T, X> *parent_matrix, unsigned index_start);

    ref operator[] (unsigned i) {
        lean_assert(i >= m_index_start);
        lean_assert(i < m_parent->dimension());
        return ref(i, *this);
    }

    int find_pivot_column_in_row(unsigned i) const;

    void swap_columns(unsigned i, unsigned j) {
        if (i != j)
            m_column_permutation.transpose_from_left(i, j);
    }

    unsigned adjust_column(unsigned  col)  const{
        return m_column_permutation.apply_reverse(col);
    }

    unsigned adjust_column_inverse(unsigned  col)  const{
        return m_column_permutation[col];
    }
    unsigned adjust_row(unsigned row)  const{
        return m_row_permutation[row];
    }

    unsigned adjust_row_inverse(unsigned row)  const{
        return m_row_permutation.apply_reverse(row);
    }

    void pivot(unsigned i, lp_settings & settings);

    void pivot_row_to_row(unsigned i, unsigned row, lp_settings & settings);;

    void divide_row_by_pivot(unsigned i);

    void update_parent_matrix(lp_settings & settings);

    void update_existing_or_delete_in_parent_matrix_for_row(unsigned i, lp_settings & settings);

    void push_new_elements_to_parent_matrix(lp_settings & settings);

    template <typename L>
    L row_by_vector_product(unsigned i, const std::vector<L> & v);

    template <typename L>
    L column_by_vector_product(unsigned j, const std::vector<L> & v);

    template <typename L>
    L row_by_indexed_vector_product(unsigned i, const indexed_vector<L> & v);

    template <typename L>
    void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings);

    template <typename L>
    void apply_from_left_to_vector(std::vector<L> & w);

    bool is_L_matrix() const;

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
        apply_from_left_local(w, settings);
    }

    void apply_from_right(indexed_vector<T> & /* w */) {
        lean_unreachable(); // not implemented
    }
    void apply_from_left(std::vector<X> & w, lp_settings & /*settings*/) {
        apply_from_left_to_vector(w);// , settings);
    }

    void apply_from_right(std::vector<T> & w);

#ifdef LEAN_DEBUG
    T get_elem (unsigned i, unsigned j) const;
    unsigned row_count() const { return m_parent->row_count();}
    unsigned column_count() const { return row_count();}
    void set_number_of_rows(unsigned) {}
    void set_number_of_columns(unsigned) {};
#endif
    void conjugate_by_permutation(permutation_matrix<T, X> & q);
};
}
