/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
namespace lean {

// This is the sum of a unit matrix and a one-column matrix
template <typename T, typename X>
class eta_matrix
    : public tail_matrix<T, X> {
#ifdef LEAN_DEBUG
    unsigned m_length;
#endif
    unsigned m_column_index;
    sparse_vector<T> m_column_vector;
    T m_diagonal_element;
public:
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

    void print() {
        print_matrix(*this);
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

    void apply_from_left(std::vector<X> & w, lp_settings & ) {
        auto w_at_column_index = w[m_column_index];
        w[m_column_index] /= m_diagonal_element;
        for (auto it = sparse_vector_iterator<T>(m_column_vector); !it.done(); it.move()) {
            w[it.index()] += w_at_column_index * it.value();
        }
    }

    template <typename L>
    void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings) {
        const L w_at_column_index = w[m_column_index];
        if (is_zero(w_at_column_index)) return;

        if (settings.abs_val_is_smaller_than_drop_tolerance(w[m_column_index] /= m_diagonal_element)) {
            w[m_column_index] = zero_of_type<L>();
            w.erase_from_index(m_column_index);
        }

        for (auto it = sparse_vector_iterator<T>(m_column_vector); !it.done(); it.move()) {
            unsigned i = it.index();
            if (is_zero(w[i])) {
                L v = w[i] = w_at_column_index * it.value();
                if (settings.abs_val_is_smaller_than_drop_tolerance(v)) {
                    w[i] = zero_of_type<L>();
                    continue;
                }
                w.m_index.push_back(i);
            } else  {
                L v = w[i] += w_at_column_index * it.value(); // todo indexed_vector
                if (settings.abs_val_is_smaller_than_drop_tolerance(v)) {
                    w[i] = zero_of_type<L>();
                    w.erase_from_index(i);
                }
            }
        }
    }

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) {
        apply_from_left_local(w, settings);
    }


    void push_back(unsigned row_index, T val ) {
        lean_assert(row_index != m_column_index);
        m_column_vector.push_back(row_index, val);
    }

    void apply_from_right(std::vector<T> & w) {
#ifdef LEAN_DEBUG
        // dense_matrix<T, X> deb(*this);
        // auto clone_w = clone_vector<T>(w, get_number_of_rows());
        // deb.apply_from_right(clone_w);
#endif
        T t = w[m_column_index] / m_diagonal_element;
        for (auto it = sparse_vector_iterator<T>(m_column_vector); !it.done(); it.move()) {
            t += w[it.index()] * it.value();
        }
        w[m_column_index] = t;
#ifdef LEAN_DEBUG
        // lean_assert(vectors_are_equal<T>(clone_w, w, get_number_of_rows()));
        // delete clone_w;
#endif
    }

    T get_elem(unsigned i, unsigned j) const {
        if (j == m_column_index){
            if (i == j) {
                return 1 / m_diagonal_element;
            }
            return m_column_vector[i];
        }

        return i == j ? numeric_traits<T>::one() : numeric_traits<T>::zero();
    }
#ifdef LEAN_DEBUG
    unsigned row_count() const { return m_length; }
    unsigned column_count() const { return m_length; }
    void set_number_of_rows(unsigned /*m*/) { }
    void set_number_of_columns(unsigned /*n*/) { }
#endif
    sparse_vector_iterator<T> get_sparse_vector_iterator() {
        return sparse_vector_iterator<T>(m_column_vector);
    }

    void divide_by_diagonal_element() {
        m_column_vector.divide(m_diagonal_element);
    }
    void conjugate_by_permutation(permutation_matrix<T, X> & p) {
        // this = p * this * p(-1)
#ifdef LEAN_DEBUG
        // auto rev = p.get_reverse();
        // auto deb = ((*this) * rev);
        // deb = p * deb;
#endif
        m_column_index = p.get_rev(m_column_index);
        for (auto & pair : m_column_vector.m_data) {
            pair.first = p.get_rev(pair.first);
        }
#ifdef LEAN_DEBUG
        // lean_assert(deb == *this);
#endif
    }
};
}
