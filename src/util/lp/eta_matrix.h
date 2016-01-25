/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/lp/tail_matrix.h"
#include "util/lp/permutation_matrix.h"
namespace lean {

// This is the sum of a unit matrix and a one-column matrix
template <typename T, typename X>
class eta_matrix
    : public tail_matrix<T, X> {
#ifdef LEAN_DEBUG
    unsigned m_length;
#endif
    unsigned m_column_index;
public:
    sparse_vector<T> m_column_vector;
    T m_diagonal_element;
#ifdef LEAN_DEBUG
    eta_matrix(unsigned column_index, unsigned length):
#else
        eta_matrix(unsigned column_index):
#endif

#ifdef LEAN_DEBUG
        m_length(length),
#endif
        m_column_index(column_index) {
    }

    void print(std::ostream & out) {
        print_matrix(*this, out);
    }

    bool is_unit() {
        return m_column_vector.size() == 0 && m_diagonal_element == 1;
    }

    void set_diagonal_element(T const & diagonal_element) {
        lean_assert(!lp_settings::is_eps_small_general(diagonal_element, 1e-12));
        m_diagonal_element = diagonal_element;
    }

    const T & get_diagonal_element() const {
        return m_diagonal_element;
    }

    void apply_from_left(std::vector<X> & w, lp_settings & );

    template <typename L>
    void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings);

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
        apply_from_left_local(w, settings);
    }


    void push_back(unsigned row_index, T val ) {
        lean_assert(row_index != m_column_index);
        m_column_vector.push_back(row_index, val);
    }

    void apply_from_right(std::vector<T> & w);

    T get_elem(unsigned i, unsigned j) const;
#ifdef LEAN_DEBUG
    unsigned row_count() const { return m_length; }
    unsigned column_count() const { return m_length; }
    void set_number_of_rows(unsigned /*m*/) { }
    void set_number_of_columns(unsigned /*n*/) { }
#endif
    void divide_by_diagonal_element() {
        m_column_vector.divide(m_diagonal_element);
    }
    void conjugate_by_permutation(permutation_matrix<T, X> & p);
};
}
