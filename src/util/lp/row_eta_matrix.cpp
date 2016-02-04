/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include "util/lp/row_eta_matrix.h"
namespace lean {
template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_left(std::vector<X> & w, lp_settings &) {
    // #ifdef LEAN_DEBUG
    //         dense_matrix<T> deb(*this);
    //         auto clone_w = clone_vector<T>(w, m_dimension);
    //         deb.apply_from_left(clone_w, settings);
    // #endif
    auto w_at_row = w[m_row];
    for (auto & it : m_row_vector.m_data) {
        w_at_row += w[it.first] * it.second;
    }
    w[m_row] = w_at_row;
    // #ifdef LEAN_DEBUG
    //         lean_assert(vectors_are_equal<T>(clone_w, w, m_dimension));
    //         delete [] clone_w;
    // #endif
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_left_local_to_T(indexed_vector<T> & w, lp_settings & settings) {
    auto w_at_row = w[m_row];
    bool was_zero_at_m_row = is_zero(w_at_row);

    for (auto & it : m_row_vector.m_data) {
        w_at_row += w[it.first] * it.second;
    }

    if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_row)){
        if (was_zero_at_m_row) {
            w.m_index.push_back(m_row);
        }
        w[m_row] = w_at_row;
    } else if (!was_zero_at_m_row){
        w[m_row] = zero_of_type<T>();
        auto it = std::find(w.m_index.begin(), w.m_index.end(), m_row);
        w.m_index.erase(it);
    }
    lean_assert(check_vector_for_small_values(w, settings));
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_left_local_to_X(indexed_vector<X> & w, lp_settings & settings) {
    auto w_at_row = w[m_row];
    bool was_zero_at_m_row = is_zero(w_at_row);

    for (auto & it : m_row_vector.m_data) {
        w_at_row += w[it.first] * it.second;
    }

    if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_row)){
        if (was_zero_at_m_row) {
            w.m_index.push_back(m_row);
        }
        w[m_row] = w_at_row;
    } else if (!was_zero_at_m_row){
        w[m_row] = zero_of_type<X>();
        auto it = std::find(w.m_index.begin(), w.m_index.end(), m_row);
        w.m_index.erase(it);
    }
    lean_assert(check_vector_for_small_values(w, settings));
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_right(std::vector<T> & w) {
    T w_row = w[m_row];
    if (numeric_traits<T>::is_zero(w_row)) return;
#ifdef LEAN_DEBUG
    // dense_matrix<T> deb(*this);
    // auto clone_w = clone_vector<T>(w, m_dimension);
    // deb.apply_from_right(clone_w);
#endif
    for (auto & it : m_row_vector.m_data) {
        w[it.first] += w_row * it.second;
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(clone_w, w, m_dimension));
    // delete clone_w;
#endif
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_right(indexed_vector<T> & w) {
    T w_row = w[m_row];
    if (numeric_traits<T>::is_zero(w_row)) return;
#ifdef LEAN_DEBUG
    //        dense_matrix<T> deb(*this);
    // auto clone_w = clone_vector<T>(w.m_data, m_dimension);
    // deb.apply_from_right(clone_w);
#endif
    for (auto & it : m_row_vector.m_data) {
        T old_val = w[it.first];
        T v = w[it.index()] += w_row * it.second;
        if (numeric_traits<T>::is_zero(old_val)) {
            w.m_index.push_back(it.index());
        } else if (numeric_traits<T>::is_zero(v)) { // it is a very rare case
            auto w_it = std::find(w.m_index.begin(), w.m_index.end(), it.index());
            lean_assert(w_it != w.m_index.end());
            w.m_index.erase(w_it);
        }
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(clone_w, w.m_data, m_dimension));
    // for (unsigned i = 0; i < m_dimension; i++) {
    //     if (!numeric_traits<T>::is_zero(w.m_data[i])) {
    //         lean_assert(std::find(w.m_index.begin(), w.m_index.end(), i) != w.m_index.end());
    //     }
    // }
    // delete clone_w;
#endif
}

template <typename T, typename X>
void row_eta_matrix<T, X>::conjugate_by_permutation(permutation_matrix<T, X> & p) {
    // this = p * this * p(-1)
#ifdef LEAN_DEBUG
    // auto rev = p.get_reverse();
    // auto deb = ((*this) * rev);
    // deb = p * deb;
#endif
    m_row = p.apply_reverse(m_row);
    // copy aside the column indices
    std::vector<unsigned> columns;
    for (auto & it : m_row_vector.m_data)
        columns.push_back(it.first);
    for (unsigned i = columns.size(); i-- > 0;)
        m_row_vector.m_data[i].first = p.get_rev(columns[i]);
#ifdef LEAN_DEBUG
    // lean_assert(deb == *this);
#endif
}
#ifdef LEAN_DEBUG
template <typename T, typename X>
T row_eta_matrix<T, X>::get_elem(unsigned row, unsigned col) const {
    if (row == m_row){
        if (col == row) {
            return numeric_traits<T>::one();
        }
        return m_row_vector[col];
    }

    return col == row ? numeric_traits<T>::one() : numeric_traits<T>::zero();
}
#endif
}

