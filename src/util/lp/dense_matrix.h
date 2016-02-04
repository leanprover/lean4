/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#ifdef LEAN_DEBUG
#include <vector>
#include "util/numerics/double.h"
#include "util/lp/matrix.h"
namespace lean {
// used for debugging purposes only
template <typename T, typename X>
class dense_matrix: public matrix<T, X> {
public:
    struct ref {
        unsigned m_i;
        dense_matrix & m_s;
        ref(unsigned i, dense_matrix & s) :m_i(i * s.m_n), m_s(s){}
        T & operator[] (unsigned j) {
            return m_s.m_values[m_i + j];
        }
        const T & operator[] (unsigned j) const {
            return m_s.m_v[m_i + j];
        }
    };
    ref operator[] (unsigned i) {
        return ref(i, *this);
    }
    unsigned m_m; // number of rows
    unsigned m_n; // number of const
    T* m_values;//
    dense_matrix(unsigned m, unsigned n);

    dense_matrix operator*=(matrix<T, X> const & a);

    dense_matrix & operator=(matrix<T, X> const & other);

    dense_matrix & operator=(dense_matrix const & other);

    dense_matrix(dense_matrix<T, X> const & other);

    dense_matrix(matrix<T, X> const & other);
    void apply_from_right(T * w);

    void apply_from_right(std::vector <T> & w);

    T * apply_from_left_with_different_dims(std::vector<T> &  w);
    void apply_from_left(std::vector<T> & w , lp_settings & ) { apply_from_left(w); }

    void apply_from_left(std::vector<T> & w);

    void apply_from_left(X * w, lp_settings & );

    void apply_from_left_to_X(std::vector<X> & w, lp_settings & );

    virtual void set_number_of_rows(unsigned /*m*/) {}
    virtual void set_number_of_columns(unsigned /*n*/) { }

    T get_elem(unsigned i, unsigned j) const { return m_values[i * m_n + j]; }

    unsigned row_count() const { return m_m; }
    unsigned column_count() const { return m_n; }

    void set_elem(unsigned i, unsigned j, const T& val) {  m_values[i * m_n + j] = val;  }

    // This method pivots row i to row i0 by muliplying row i by
    //   alpha and adding it to row i0.
    void pivot_row_to_row(unsigned i, T alpha, unsigned i0,
                          double & pivot_epsilon);

    void swap_columns(unsigned a, unsigned b);

    void swap_rows(unsigned a, unsigned b);

    void multiply_row_by_constant(unsigned row, T & t);

    ~dense_matrix() {  delete [] m_values; }
};
template <typename T, typename X>
dense_matrix<T, X> operator* (matrix<T, X> & a, matrix<T, X> & b);
}
#endif
