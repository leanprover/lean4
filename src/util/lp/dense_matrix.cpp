/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#ifdef LEAN_DEBUG
#include <vector>
#include "util/lp/dense_matrix.h"
namespace lean {
template <typename T, typename X> dense_matrix<T, X>::dense_matrix(unsigned m, unsigned n) : m_m(m), m_n(n) {
    m_values = new T[m * n];
    for (unsigned i = 0; i < m * n; i ++)
        m_values[i] = numeric_traits<T>::zero();
}

template <typename T, typename X> dense_matrix<T, X> dense_matrix<T, X>::operator*=(matrix<T, X> const & a) {
    lean_assert(column_count() == a.row_count());
    dense_matrix c(row_count(), a.column_count());
    for (unsigned i = 0; i < row_count(); i++) {
        for (unsigned j = 0; j < a.column_count(); j++) {
            T v = numeric_traits<T>::zero();
            for (unsigned k = 0; k < a.column_count(); k++) {
                v += get_elem(i, k) * a(k, j);
            }
            c.set_elem(i, j, v);
        }
    }
    *this = c;
    return *this;
}
template <typename T, typename X> dense_matrix<T, X>&
dense_matrix<T, X>::operator=(matrix<T, X> const & other){
    if ( this == & other)
        return *this;
    m_values = new T[m_m * m_n];
    for (unsigned i = 0; i < m_m; i ++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other.get_elem(i, j);
    return *this;
}

template <typename T, typename X> dense_matrix<T, X>&
dense_matrix<T, X>::operator=(dense_matrix const & other){
    if ( this == & other)
        return *this;
    m_m = other.m_m;
    m_n = other.m_n;
    delete [] m_values;
    m_values = new T[m_m * m_n];
    for (unsigned i = 0; i < m_m; i ++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other.get_elem(i, j);
    return *this;
}

template <typename T, typename X> dense_matrix<T, X>::dense_matrix(dense_matrix<T, X> const & other) : m_m(other.row_count()), m_n(other.column_count()) {
    m_values = new T[m_m * m_n];
    for (unsigned i = 0; i < m_m; i ++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other.get_elem(i, j);
}

template <typename T, typename X> dense_matrix<T, X>::dense_matrix(matrix<T, X> const & other) :
    m_m(other.row_count()),
    m_n(other.column_count()) {
    m_values = new T[m_m * m_n];
    for (unsigned i = 0; i < m_m; i++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other.get_elem(i, j);
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_right(T * w) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(j, i);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i++) {
        w[i] = t[i];
    }
    delete [] t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_right(std::vector <T> & w) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(j, i);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i++) {
        w[i] = t[i];
    }
    delete [] t;
}
template <typename T, typename X> T* dense_matrix<T, X>::
apply_from_left_with_different_dims(std::vector<T> &  w) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_n; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    return t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_left(std::vector<T> & w) {
    T * t = new T[m_m];
    for (unsigned i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (unsigned j = 0; j < m_m; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    for (unsigned i = 0; i < m_m; i ++) {
        w[i] = t[i];
    }
    delete [] t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_left(X * w, lp_settings & ) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i ++) {
        w[i] = t[i];
    }
    delete [] t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_left_to_X(std::vector<X> & w, lp_settings & ) {
    std::vector<X> t(m_m);
    for (int i = 0; i < m_m; i ++) {
        X v = zero_of_type<X>();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i ++) {
        w[i] = t[i];
    }
}

// This method pivots row i to row i0 by muliplying row i by
//   alpha and adding it to row i0.
template <typename T, typename X> void dense_matrix<T, X>::pivot_row_to_row(unsigned i, T alpha, unsigned i0,
                                                                            double & pivot_epsilon) {
    T _0 = numeric_traits<T>::zero();
    for (unsigned j = 0; j < m_n; j++) {
        m_values[i0 * m_n + j] += m_values[i * m_n + j] * alpha;
        if (fabs(m_values[i0 + m_n + j]) < pivot_epsilon) {
            m_values[i0 + m_n + j] = _0;
        }
    }
}

template <typename T, typename X> void dense_matrix<T, X>::swap_columns(unsigned a, unsigned b) {
    for (unsigned i = 0; i < m_m; i++) {
        T t = get_elem(i, a);
        set_elem(i, a, get_elem(i, b));
        set_elem(i, b, t);
    }
}

template <typename T, typename X> void dense_matrix<T, X>::swap_rows(unsigned a, unsigned b) {
    for (unsigned i = 0; i < m_n; i++) {
        T t = get_elem(a, i);
        set_elem(a, i, get_elem(b, i));
        set_elem(b, i, t);
    }
}

template <typename T, typename X> void dense_matrix<T, X>::multiply_row_by_constant(unsigned row, T & t) {
    for (unsigned i = 0; i < m_n; i++) {
        set_elem(row, i, t * get_elem(row, i));
    }
}

template <typename T, typename X>
dense_matrix<T, X> operator* (matrix<T, X> & a, matrix<T, X> & b){
    dense_matrix<T, X> ret(a.row_count(), b.column_count());
    for (unsigned i = 0; i < ret.m_m; i++)
        for (unsigned j = 0; j< ret.m_n; j++) {
            T v = numeric_traits<T>::zero();
            for (unsigned k = 0; k < a.column_count(); k ++){
                v += (a.get_elem(i, k) * b.get_elem(k, j));
            }
            ret.set_elem(i, j, v);
        }
    return  ret;
}
}
#endif
