/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include <utility>
#include <set>
#include "util/lp/static_matrix.h"
namespace lean {
// each assignment for this matrix should be issued only once!!!
template <typename T, typename X>
void  static_matrix<T, X>::init_row_columns(unsigned m, unsigned n) {
    lean_assert(m_rows.size() == 0 && m_columns.size() == 0);
    for (unsigned i = 0; i < m; i++){
        m_rows.push_back(row_strip());
    }
    for (unsigned j = 0; j < n; j++){
        m_columns.push_back(column_strip());
    }
}

// constructor that copies columns of the basis from A
template <typename T, typename X>
static_matrix<T, X>::static_matrix(static_matrix const &A, unsigned * /* basis */) :
    m_work_pivot_vector(A.row_count(), numeric_traits<T>::zero()) {
    unsigned m = A.row_count();
    init_row_columns(m, m);
    while (m--) {
        for (auto & col : A.m_columns[m]){
            set(col.m_i, m, A.get_value_of_column_cell(col));
        }
    }
}

template <typename T, typename X>    void static_matrix<T, X>::clear() {
    m_work_pivot_vector.clear();
    m_rows.clear();
    m_columns.clear();
#ifdef LEAN_DEBUG
    m_domain.clear();
#endif
}

template <typename T, typename X>    void static_matrix<T, X>::init_work_pivot_vector(unsigned m) {
    while (m--) m_work_pivot_vector.push_back(numeric_traits<T>::zero());
}

template <typename T, typename X>    void static_matrix<T, X>::init_empty_matrix(unsigned m, unsigned n) {
    init_work_pivot_vector(m);
    init_row_columns(m, n);
}
template <typename T, typename X>
template <typename L>
L static_matrix<T, X>::dot_product_with_row(unsigned row, const std::vector<L> & w) {
    L ret = zero_of_type<L>();
    lean_assert(row < m_rows.size());
    for (auto & it : m_rows[row]) {
        ret += w[it.m_j] * it.get_val();
    }
    return ret;
};

template <typename T, typename X>    unsigned static_matrix<T, X>::lowest_row_in_column(unsigned col) {
    lean_assert(col < column_count());
    column_strip & colstrip = m_columns[col];
    lean_assert(colstrip.size() > 0);
    unsigned ret = 0;
    for (auto & t : colstrip) {
        if (t.m_i > ret) {
            ret = t.m_i;
        }
    }
    return ret;
}

template <typename T, typename X>    T static_matrix<T, X>::dot_product_with_column(const std::vector<T> & y, unsigned j) const {
    lean_assert(j < column_count());
    T ret = numeric_traits<T>::zero();
    for (auto & it : m_columns[j]) {
        ret += y[it.m_i] * it.m_value; // get_value_of_column_cell(it);
    }
    return ret;
}

template <typename T, typename X>    void static_matrix<T, X>::add_columns_at_the_end(unsigned delta) {
    for (unsigned i = 0; i < delta; i++)
        add_column();
}

template <typename T, typename X>    void static_matrix<T, X>::forget_last_columns(unsigned how_many_to_forget) {
    lean_assert(m_columns.size() >= how_many_to_forget);
    unsigned j = column_count() - 1;
    for (; how_many_to_forget > 0; how_many_to_forget--) {
        remove_last_column(j --);
    }
}

template <typename T, typename X>    void static_matrix<T, X>::remove_last_column(unsigned j) {
    column_strip & col = m_columns.back();
    for (auto & it : col) {
        auto & row = m_rows[it.m_i];
        unsigned offset = row.size() - 1;
        for (auto row_it = row.rbegin(); row_it != row.rend(); row_it ++) {
            if (row_it->m_j == j) {
                row.erase(row.begin() + offset);
                break;
            }
            offset--;
        }
    }
    m_columns.pop_back();
}

template <typename T, typename X>
void static_matrix<T, X>::scale_row(unsigned row, T const & alpha) {
    for (auto & t : m_rows[row]) {
        t.set_val(t.get_val() * alpha);
        m_columns[t.m_j][t.m_offset].m_value *= alpha;
    }
}

template <typename T, typename X>
void static_matrix<T, X>::divide_row_by_constant(unsigned row, T const & alpha) {
    for (auto & t : m_rows[row]) {
        t.set_val(t.get_val() / alpha);
        m_columns[t.m_j][t.m_offset].m_value /= alpha;
    }
}

template <typename T, typename X>
void static_matrix<T, X>::scale_column(unsigned column, T const & alpha) {
    for (auto & t : m_columns[column]) {
        t.m_value *= alpha;
        auto & r = m_rows[t.m_i][t.m_offset];
        r.set_val(r.get_val() *= alpha);
    }
}

#ifdef LEAN_DEBUG
template <typename T, typename X>    void static_matrix<T, X>::regen_domain() {
    m_domain.clear();
    for (int i = 0; i < m_rows.size(); i++){
        for (auto & t : m_rows[i]) {
            m_domain.insert(std::make_pair(i, t.m_j));
        }
    }
}
#endif

template <typename T, typename X>    void static_matrix<T, X>::set(unsigned row, unsigned col, T const & val) {
    if (numeric_traits<T>::is_zero(val)) return;
    lean_assert(row < row_count() && col < column_count());
#ifdef LEAN_DEBUG
    pair<unsigned, unsigned> p(row, col);
    lean_assert(m_domain.find(p) == m_domain.end());
    m_domain.insert(p);
#endif
    auto & r = m_rows[row];
    unsigned offs_in_cols = m_columns[col].size();
    m_columns[col].push_back(make_column_cell(row, r.size(), val));
    r.push_back(make_row_cell(col, offs_in_cols, val));
}

template <typename T, typename X>
std::set<pair<unsigned, unsigned>>  static_matrix<T, X>::get_domain() {
    std::set<pair<unsigned, unsigned>> ret;
    for (unsigned i = 0; i < m_rows.size(); i++) {
        for (auto it : m_rows[i]) {
            ret.insert(std::make_pair(i, it.m_j));
        }
    }
    return ret;
}


template <typename T, typename X>    void static_matrix<T, X>::copy_column_to_vector (unsigned j, indexed_vector<T> & v) const {
    lean_assert(j < m_columns.size());
    for (auto & it : m_columns[j]) {
        if (!is_zero(it.m_value))
            v.set_value(it.m_value, it.m_i);
    }
}

template <typename T, typename X>    void static_matrix<T, X>::copy_column_to_vector (unsigned j, std::vector<T> & v) const {
    v.resize(row_count(), numeric_traits<T>::zero());
    for (auto & it : m_columns[j]) {
        if (!is_zero(it.m_value))
            v[it.m_i]=it.m_value;
    }
}

template <typename T, typename X>    void static_matrix<T, X>::add_column_to_vector (const T & a, unsigned j, T * v) const {
    for (auto & it : m_columns[j]) {
        v[it.m_i] += a * it.m_value;
    }
}

template <typename T, typename X>    T static_matrix<T, X>::get_max_abs_in_row(unsigned row) const {
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_rows[row]) {
        T a = abs(t.get_val());
        if (a  > ret) {
            ret = a;
        }
    }
    return ret;
}

template <typename T, typename X>    T static_matrix<T, X>::get_min_abs_in_row(unsigned row) const {
    bool first_time = true;
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_rows[row]) {
        T a = abs(t.get_val());
        if (first_time) {
            ret = a;
            first_time = false;
        } else if (a  < ret) {
            ret = a;
        }
    }
    return ret;
}


template <typename T, typename X>    T static_matrix<T, X>::get_max_abs_in_column(unsigned column) const {
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_columns[column]) {
        T a = abs(t.m_value);
        if (a  > ret) {
            ret = a;
        }
    }
    return ret;
}

template <typename T, typename X>     T static_matrix<T, X>::get_min_abs_in_column(unsigned column) const {
    bool first_time = true;
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_columns[column]) {
        T a = abs(t.m_value);
        if (first_time) {
            first_time = false;
            ret = a;
        } else if (a  < ret) {
            ret = a;
        }
    }
    return ret;
}

#ifdef LEAN_DEBUG
template <typename T, typename X>    void static_matrix<T, X>::check_consistency() {
    std::unordered_map<std::pair<unsigned, unsigned>, T> by_rows;
    for (int i = 0; i < m_rows.size(); i++){
        for (auto & t : m_rows[i]) {
            pair<unsigned, unsigned> p(i, t.m_j);
            lean_assert(by_rows.find(p) == by_rows.end());
            by_rows[p] = t.get_val();
        }
    }
    std::unordered_map<pair<unsigned, unsigned>, T> by_cols;
    for (int i = 0; i < m_columns.size(); i++){
        for (auto & t : m_columns[i]) {
            pair<unsigned, unsigned> p(t.m_i, i);
            lean_assert(by_cols.find(p) == by_cols.end());
            by_cols[p] = get_value_of_column_cell(t);
        }
    }
    lean_assert(by_rows.size() == by_cols.size());

    for (auto & t : by_rows) {
        auto ic = by_cols.find(t.first);
        if (ic == by_cols.end()){
            std::cout << "rows have pair (" << t.first.first <<"," << t.first.second
                      << "), but columns don't " << std::endl;
        }
        lean_assert(ic != by_cols.end());
        lean_assert(t.second == ic->second);
    }
}
#endif


template <typename T, typename X>    void static_matrix<T, X>::cross_out_row(unsigned k) {
#ifdef LEAN_DEBUG
    check_consistency();
#endif
    cross_out_row_from_columns(k, m_rows[k]);
    fix_row_indices_in_each_column_for_crossed_row(k);
    m_rows.erase(m_rows.begin() + k);
#ifdef LEAN_DEBUG
    regen_domain();
    check_consistency();
#endif
}


template <typename T, typename X>    void static_matrix<T, X>::fix_row_indices_in_each_column_for_crossed_row(unsigned k) {
    for (unsigned j = 0; j < m_columns.size(); j++) {
        auto & col = m_columns[j];
        for (int i = 0; i < col.size(); i++) {
            if (col[i].m_i > k) {
                col[i].m_i--;
            }
        }
    }
}

template <typename T, typename X>    void static_matrix<T, X>::cross_out_row_from_columns(unsigned k, row_strip & row) {
    for (auto & t : row) {
        cross_out_row_from_column(t.m_j, k);
    }
}

template <typename T, typename X>    void static_matrix<T, X>::cross_out_row_from_column(unsigned col, unsigned k) {
    auto & s = m_columns[col];
    for (unsigned i = 0; i < s.size(); i++) {
        if (s[i].m_i == k) {
            s.erase(s.begin() + i);
            break;
        }
    }
}

template <typename T, typename X>    T static_matrix<T, X>::get_elem(unsigned i, unsigned j) const { // should not be used in efficient code !!!!
    for (auto & t : m_rows[i]) {
        if (t.m_j == j) {
            return t.get_val();
        }
    }
    return numeric_traits<T>::zero();
}


template <typename T, typename X>    void static_matrix<T, X>::scan_row_to_work_vector(unsigned i) {
    for (auto & rc : m_rows[i]) {
        m_work_pivot_vector[rc.m_j] = rc.get_val();
    }
}

template <typename T, typename X>    void static_matrix<T, X>::clean_row_work_vector(unsigned i) {
    for (auto & rc : m_rows[i]) {
        m_work_pivot_vector[rc.m_j] = numeric_traits<T>::zero();
    }
}


template <typename T, typename X>    T static_matrix<T, X>::get_balance() const {
    T ret = zero_of_type<T>();
    for (unsigned i = 0; i < row_count();  i++) {
        ret += get_row_balance(i);
    }
    return ret;
}

template <typename T, typename X>    T static_matrix<T, X>::get_row_balance(unsigned row) const {
    T ret = zero_of_type<T>();
    for (auto & t : m_rows[row]) {
        if (numeric_traits<T>::is_zero(t.get_val())) continue;
        T a = abs(t.get_val());
        numeric_traits<T>::log(a);
        ret += a * a;
    }
    return ret;
}
#ifdef LEAN_DEBUG
template <typename T, typename X> bool static_matrix<T, X>::col_val_equal_to_row_val() const {
    for (auto & r : m_rows) {
        for (auto & rc : r) {
            lean_assert(rc.get_val() == m_columns[rc.m_j][rc.m_offset].m_value);
        }
    }
    return true;
}
#endif
}
