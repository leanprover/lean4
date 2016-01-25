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
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include <string>
#include "util/lp/sparse_vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/permutation_matrix.h"
namespace lean {
    // This is the sum of a unit matrix and a lower triangular matrix
    // with non-zero elements only in one column
template <typename T, typename X>
class row_eta_matrix
        : public tail_matrix<T, X> {
#ifdef LEAN_DEBUG
    unsigned m_dimension;
#endif
    unsigned m_row_start;
    unsigned m_row;
    sparse_vector<T> m_row_vector;
public:
#ifdef LEAN_DEBUG
    row_eta_matrix(unsigned row_start, unsigned row, unsigned dim):
#else
    row_eta_matrix(unsigned row_start, unsigned row):
#endif

#ifdef LEAN_DEBUG
    m_dimension(dim),
#endif
    m_row_start(row_start), m_row(row) {
        lean_assert(dim > 0);
    }

    void print(std::ostream & out) {
        print_matrix(*this, out);
    }

    const T & get_diagonal_element() const {
        return m_row_vector.m_data[m_row];
    }

    void apply_from_left(std::vector<X> & w, lp_settings &);

    void apply_from_left_local_to_T(indexed_vector<T> & w, lp_settings & settings);
    void apply_from_left_local_to_X(indexed_vector<X> & w, lp_settings & settings);

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
        apply_from_left_local_to_T(w, settings);
    }

    void push_back(unsigned row_index, T val ) {
        m_row_vector.push_back(row_index, val);
    }

    void apply_from_right(std::vector<T> & w);
    void apply_from_right(indexed_vector<T> & w);

    void conjugate_by_permutation(permutation_matrix<T, X> & p);
#ifdef LEAN_DEBUG
    T get_elem(unsigned row, unsigned col) const;
    unsigned row_count() const { return m_dimension; }
    unsigned column_count() const { return m_dimension; }
    void set_number_of_rows(unsigned /*m*/) { }
    void set_number_of_columns(unsigned /*n*/) { }
#endif
}; // end of row_eta_matrix
}
