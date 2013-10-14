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

namespace lean {
    // This is the sum of a unit matrix and a lower triangular matrix
    // with non-zero elements only in one column
template <typename T, typename X>
class row_eta_matrix
        : public tail_matrix<T, X> {
#ifndef NDEBUG
    unsigned m_dimension;
#endif
    unsigned m_row_start;
    unsigned m_row;
    sparse_vector<T> m_row_vector;
public:
#ifndef NDEBUG
    row_eta_matrix(unsigned row_start, unsigned row, unsigned dim):
#else
    row_eta_matrix(unsigned row_start, unsigned row):
#endif

#ifndef NDEBUG
    m_dimension(dim),
#endif
    m_row_start(row_start), m_row(row) {
        lean_assert(dim > 0);
    }

    void print() {
        print_matrix(*this);
    }

    const T & get_diagonal_element() const {
        return m_row_vector.m_data[m_row];
    }

    void apply_from_left(vector<X> & w, lp_settings &
#ifndef NDEBUG
                         //  settings
#endif
) {
// #ifndef NDEBUG
//         dense_matrix<T> deb(*this);
//         auto clone_w = clone_vector<T>(w, m_dimension);
//         deb.apply_from_left(clone_w, settings);
// #endif
        auto w_at_row = w[m_row];
        for (auto it = sparse_vector_iterator<T>(m_row_vector); !it.done(); it.move()) {
            w_at_row += w[it.index()] * it.value();
        }
        w[m_row] = w_at_row;
// #ifndef NDEBUG
//         lean_assert(vectors_are_equal<T>(clone_w, w, m_dimension));
//         delete [] clone_w;
// #endif
    }

    template <typename L>
    void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings) {
#ifndef NDEBUG
        // dense_matrix<T> deb(*this);
        // auto clone_w = clone_vector<T>(w.m_data, m_dimension);
        // deb.apply_from_left(clone_w);
#endif
        auto w_at_row = w[m_row];
        bool was_zero_at_m_row = is_zero(w_at_row);

        for (auto it = sparse_vector_iterator<T>(m_row_vector); !it.done(); it.move()) {
            w_at_row += w[it.index()] * it.value();
        }

        if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_row)){
            if (was_zero_at_m_row) {
                w.m_index.push_back(m_row);
            }
            w[m_row] = w_at_row;
        } else if (!was_zero_at_m_row){
            w[m_row] = zero_of_type<L>();
            auto it = std::find(w.m_index.begin(), w.m_index.end(), m_row);
            w.m_index.erase(it);
        }
        lean_assert(check_vector_for_small_values(w, settings));
#ifndef NDEBUG
        // lean_assert(vectors_are_equal<T>(clone_w, w.m_data, m_dimension));
        // delete clone_w;
#endif
    }

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
        apply_from_left_local(w, settings);
    }

    void push_back(unsigned row_index, T val ) {
        m_row_vector.push_back(row_index, val);
    }

    void apply_from_right(vector<T> & w) {
        T w_row = w[m_row];
        if (numeric_traits<T>::is_zero(w_row)) return;
#ifndef NDEBUG
        // dense_matrix<T> deb(*this);
        // auto clone_w = clone_vector<T>(w, m_dimension);
        // deb.apply_from_right(clone_w);
#endif
        for (auto it = sparse_vector_iterator<T>(m_row_vector); !it.done(); it.move()) {
            w[it.index()] += w_row * it.value();
        }
#ifndef NDEBUG
        // lean_assert(vectors_are_equal<T>(clone_w, w, m_dimension));
        // delete clone_w;
#endif
    }

    void apply_from_right(indexed_vector<T> & w) {
        T w_row = w[m_row];
        if (numeric_traits<T>::is_zero(w_row)) return;
#ifndef NDEBUG
        //        dense_matrix<T> deb(*this);
        // auto clone_w = clone_vector<T>(w.m_data, m_dimension);
        // deb.apply_from_right(clone_w);
#endif
        for (auto it = sparse_vector_iterator<T>(m_row_vector); !it.done(); it.move()) {
            T old_val = w[it.index()];
            T v = w[it.index()] += w_row * it.value();
            if (numeric_traits<T>::is_zero(old_val)) {
                w.m_index.push_back(it.index());
            } else if (numeric_traits<T>::is_zero(v)) { // it is a very rare case
                auto w_it = std::find(w.m_index.begin(), w.m_index.end(), it.index());
                lean_assert(w_it != w.m_index.end());
                w.m_index.erase(w_it);
            }
        }
#ifndef NDEBUG
        // lean_assert(vectors_are_equal<T>(clone_w, w.m_data, m_dimension));
        // for (unsigned i = 0; i < m_dimension; i++) {
        //     if (!numeric_traits<T>::is_zero(w.m_data[i])) {
        //         lean_assert(std::find(w.m_index.begin(), w.m_index.end(), i) != w.m_index.end());
        //     }
        // }
        // delete clone_w;
#endif
    }

    void conjugate_by_permutation(permutation_matrix<T, X> & p) {
        // this = p * this * p(-1)
#ifndef NDEBUG
        // auto rev = p.get_reverse();
        // auto deb = ((*this) * rev);
        // deb = p * deb;
#endif
        m_row = p.apply_reverse(m_row);
        // copy aside the column indices
        vector<unsigned> columns;
        for (auto it = sparse_vector_iterator<T>(m_row_vector); !it.done(); it.move()) {
            columns.push_back(it.index());
        }
        for (unsigned i = columns.size(); i-- > 0;) {
            m_row_vector.m_data[i].first = p.get_rev(columns[i]);
        }
#ifndef NDEBUG
        // lean_assert(deb == *this);
#endif
    }

    T get_elem(unsigned row, unsigned col) const {
        if (row == m_row){
            if (col == row) {
                return numeric_traits<T>::one();
            }
            return m_row_vector[col];
        }

        return col == row ? numeric_traits<T>::one() : numeric_traits<T>::zero();
    }
#ifndef NDEBUG
    unsigned row_count() const { return m_dimension; }
    unsigned column_count() const { return m_dimension; }
    void set_number_of_rows(unsigned /*m*/) { }
    void set_number_of_columns(unsigned /*n*/) { }
#endif
}; // end of row_eta_matrix
}
