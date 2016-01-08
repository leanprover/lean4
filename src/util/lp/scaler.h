/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <math.h>
#include <algorithm>
#include <stdio.h>      /* printf, fopen */
#include <stdlib.h>     /* exit, EXIT_FAILURE */
#include "util/numerics/double.h"
namespace lean {
// for scaling an LP
template <typename T, typename X>
class scaler {
    std::vector<X> & m_b; // right side
    static_matrix<T, X> &m_A; // the constraint matrix
    const T &  m_scaling_minimum;
    const T & m_scaling_maximum;
    std::vector<T>& m_column_scale;
    lp_settings & m_settings;
public:
    // constructor
    scaler(std::vector<X> & b, static_matrix<T, X> &A, const T & scaling_minimum, const T & scaling_maximum, std::vector<T> & column_scale,
           lp_settings & settings):
        m_b(b),
        m_A(A),
        m_scaling_minimum(scaling_minimum),
        m_scaling_maximum(scaling_maximum),
        m_column_scale(column_scale),
        m_settings(settings) {
        lean_assert(m_column_scale.size() == 0);
        m_column_scale.resize(m_A.column_count(), numeric_traits<T>::one());
    }

    T right_side_balance() {
        T ret = zero_of_type<T>();
        unsigned i = m_A.row_count();
        while (i--) {
            T rs = abs(convert_struct<T, X>::convert(m_b[i]));
            if (!is_zero<T>(rs)) {
                numeric_traits<T>::log(rs);
                ret += rs * rs;
            }
        }
        return ret;
    }

    T get_balance() {
        return m_A.get_balance();
    }

    T A_min() const {
        T min = zero_of_type<T>();
        for (unsigned i = 0; i < m_A.row_count(); i++) {
            T t = m_A.get_min_abs_in_row(i);
            min = i == 0 ? t : std::min(t, min);
        }
        return min;
    }

    T A_max() const {
        T max = zero_of_type<T>();
        for (unsigned i = 0; i < m_A.row_count(); i++) {
            T t = m_A.get_max_abs_in_row(i);
            max = i == 0? t : std::max(t, max);
        }
        return max;
    }

    T get_A_ratio() const {
        T min = A_min();
        T max = A_max();
        T ratio = max / min;
        return ratio;
    }

    T get_max_ratio_on_rows() const {
        T ret = T(1);
        unsigned i = m_A.row_count();
        while (i--) {
            T t = m_A.get_max_abs_in_row(i)/m_A.get_min_abs_in_row(i);
            if (t > ret)
                ret = t;
        }
        return ret;
    }

    T get_max_ratio_on_columns() const {
        T ret = T(1);
        unsigned i = m_A.column_count();
        while (i--) {
            T t = m_A.get_max_abs_in_column(i)/m_A.get_min_abs_in_column(i);
            if (t > ret)
                ret = t;
        }
        return ret;
    }

    void scale_rows_with_geometric_mean() {
        unsigned i = m_A.row_count();
        while (i--) {
            T max = m_A.get_max_abs_in_row(i);
            T min = m_A.get_min_abs_in_row(i);
            lean_assert(max > zero_of_type<T>() && min > zero_of_type<T>());
            T gm = T(sqrt(numeric_traits<T>::get_double(max*min)));
            m_A.divide_row_by_constant(i, gm);
            m_b[i] /= gm;
        }
    }

    void scale_columns_with_geometric_mean() {
        unsigned i = m_A.column_count();
        while (i--) {
            T max = m_A.get_max_abs_in_column(i);
            T min = m_A.get_min_abs_in_column(i);
            T gm = T(1)/T(sqrt(numeric_traits<T>::get_double(max*min)));
            m_A.scale_column(i, gm);
            m_column_scale[i]*=gm;
        }
    }

    void scale_once_for_ratio() {
        T max_ratio_on_rows = get_max_ratio_on_rows();
        T max_ratio_on_columns = get_max_ratio_on_columns();
        bool scale_rows_first = max_ratio_on_rows > max_ratio_on_columns;
        // if max_ratio_on_columns is the largerst then the rows are in worser shape then columns
        if (scale_rows_first) {
            scale_rows_with_geometric_mean();
            scale_columns_with_geometric_mean();
        } else {
            scale_columns_with_geometric_mean();
            scale_rows_with_geometric_mean();
        }
    }

    bool scale_with_ratio() {
        T ratio = get_A_ratio();
        // The ratio is greater than or equal to one. We would like to diminish it and bring it as close to 1 as possible
        unsigned reps = 20;
        do {
            scale_once_for_ratio();
            T new_r = get_A_ratio();
            if (new_r >= T(0.9) * ratio)
                break;
        } while (reps--);

        bring_rows_and_columns_maximums_to_one();
        return true;
    }

    void bring_row_maximums_to_one() {
        unsigned i = m_A.row_count();
        while (i--) {
            T t = m_A.get_max_abs_in_row(i);
            m_A.divide_row_by_constant(i, t);
            m_b[i] /= t;
        }
    }

    void bring_column_maximums_to_one() {
        unsigned i = m_A.column_count();
        while (i--) {
            T t = T(1) / m_A.get_max_abs_in_column(i);
            m_A.scale_column(i, t);
            m_column_scale[i] *= t;
        }
    }

    void bring_rows_and_columns_maximums_to_one() {
        if (get_max_ratio_on_rows() > get_max_ratio_on_columns()) {
            bring_row_maximums_to_one();
            bring_column_maximums_to_one();
        } else {
            bring_column_maximums_to_one();
            bring_row_maximums_to_one();
        }
    }

    bool scale_with_log_balance() {
        T balance = get_balance();
        T balance_before_scaling = balance;
        // todo : analyze the scale order : rows-columns, or columns-rows. Iterate if needed
        for (int i = 0; i < 10; i++) {
            scale_rows();
            scale_columns();
            T nb = get_balance();
            if (nb < T(0.9) * balance) {
                balance = nb;
            } else {
                balance = nb;
                break;
            }
        }
        return balance <= balance_before_scaling;
    }
    // Returns true if and only if the scaling was successful.
    // It is the caller responsibility to restore the matrix
    bool scale() {
        if (numeric_traits<T>::precise())  return true;
        if (m_settings.scale_with_ratio)
            return scale_with_ratio();
        return scale_with_log_balance();
    }

    void scale_rows() {
        for (unsigned i = 0; i < m_A.row_count(); i++)
            scale_row(i);
    }

    void scale_row(unsigned i) {
        T row_max = std::max(m_A.get_max_abs_in_row(i), abs(convert_struct<T, X>::convert(m_b[i])));
        T alpha = numeric_traits<T>::one();
        if (numeric_traits<T>::is_zero(row_max)) {
            return;
        }
        if (numeric_traits<T>::get_double(row_max) < m_scaling_minimum) {
            do {
                alpha *= 2;
                row_max *= 2;
            } while (numeric_traits<T>::get_double(row_max) < m_scaling_minimum);
            m_A.scale_row(i, alpha);
            m_b[i] *= alpha;
        } else if (numeric_traits<T>::get_double(row_max) > m_scaling_maximum) {
            do {
                alpha /= 2;
                row_max /= 2;
            } while (numeric_traits<T>::get_double(row_max) > m_scaling_maximum);
            m_A.scale_row(i, alpha);
            m_b[i] *= alpha;
        }
    }

    void scale_column(unsigned i){
        T column_max = m_A.get_max_abs_in_column(i);
        T alpha = numeric_traits<T>::one();

        if (numeric_traits<T>::is_zero(column_max)){
            return; // the column has zeros only
        }

        if (numeric_traits<T>::get_double(column_max) < m_scaling_minimum) {
            do {
                alpha *= 2;
                column_max *= 2;
            } while (numeric_traits<T>::get_double(column_max) < m_scaling_minimum);
        } else if (numeric_traits<T>::get_double(column_max) > m_scaling_maximum) {
            do {
                alpha /= 2;
                column_max /= 2;
            } while (numeric_traits<T>::get_double(column_max) > m_scaling_maximum);
        } else {
            return;
        }
        m_A.scale_column(i, alpha);
        m_column_scale[i] = alpha;
    }

    void scale_columns() {
        for (unsigned i = 0; i < m_A.column_count(); i++) {
            scale_column(i);
        }
    }
};
}
