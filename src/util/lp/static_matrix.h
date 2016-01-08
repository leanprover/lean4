/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include <set>
#include "util/lp/sparse_vector.h"
#include <unordered_map>
#include <utility>
#include "util/lp/matrix_domain.h"
#include "util/lp/indexed_vector.h"

namespace lean {
template <typename T>
struct column_cell {
    unsigned m_i; // points to the row
    unsigned m_offset;  // the offset of the element in the matrix row
    T m_value;
    column_cell(unsigned i, unsigned offset, T v) : m_i(i), m_offset(offset), m_value(v) {
    }
};

template <typename T>
class row_cell {
public:
    unsigned m_j; // points to the column
    unsigned m_offset; // offset in column
    row_cell(unsigned j, unsigned offset, T const & val) : m_j(j), m_offset(offset), m_value(val) {
    }
    const T & get_val() const { return m_value;}
    T & get_val() { return m_value;}
    void set_val(T v) {
        m_value = v;
    }
private:
    T m_value;
};



    // each assignment for this matrix should be issued only once!!!
template <typename T, typename X>
class static_matrix
#ifdef LEAN_DEBUG
    : public matrix<T, X>
#endif
{
#ifdef LEAN_DEBUG
    std::set<pair<unsigned, unsigned>> m_domain;
#endif
public:
    typedef std::vector<row_cell<T>> row_strip;
    typedef std::vector<column_cell<T>> column_strip;
    std::vector<T> m_work_pivot_vector;

    std::vector<row_strip> m_rows;
    std::vector<column_strip> m_columns;
    // starting inner classes
    class ref {
        static_matrix & m_matrix;
        unsigned m_row;
        unsigned m_col;
    public:
        ref(static_matrix & m, unsigned row, unsigned col):m_matrix(m), m_row(row), m_col(col) {}
        ref & operator=(T const & v) { m_matrix.set( m_row, m_col, v); return *this; }

        ref & operator=(ref const & v) { m_matrix.set(m_row, m_col, v.m_matrix.get(v.m_row, v.m_col)); return *this; }

        operator T () const { return m_matrix.get_elem(m_row, m_col); }
    };

    class ref_row {
        static_matrix & m_matrix;
        unsigned        m_row;
    public:
        ref_row(static_matrix & m, unsigned row):m_matrix(m), m_row(row) {}
        ref operator[](unsigned col) const { return ref(m_matrix, m_row, col); }
    };

public:
    void init_row_columns(unsigned m, unsigned n) {
        lean_assert(m_rows.size() == 0 && m_columns.size() == 0);
        for (unsigned i = 0; i < m; i++){
            m_rows.push_back(row_strip());
        }
        for (unsigned j = 0; j < n; j++){
            m_columns.push_back(column_strip());
        }
    }

        // constructor with no parameters
    static_matrix() {}

    // constructor
    static_matrix(unsigned m, unsigned n): m_work_pivot_vector(m, numeric_traits<T>::zero())  {
        init_row_columns(m, n);
    }
    // constructor that copies columns of the basis from A
    static_matrix(static_matrix const &A, unsigned * basis) :
        m_work_pivot_vector(A.row_count(), numeric_traits<T>::zero()) {
        unsigned m = A.row_count();
        init_row_columns(m, m);
        while (m--) {
            for (auto & col : A.m_columns[m]){
                set(col.m_i, m, A.get_value_of_column_cell(col));
            }
        }
    }

    void clear() {
        m_work_pivot_vector.clear();
        m_rows.clear();
        m_columns.clear();
#ifdef LEAN_DEBUG
        m_domain.clear();
#endif
    }

    void init_work_pivot_vector(unsigned m) {
        while (m--) m_work_pivot_vector.push_back(numeric_traits<T>::zero());
    }

    void init_empty_matrix(unsigned m, unsigned n) {
        init_work_pivot_vector(m);
        init_row_columns(m, n);
    }

    unsigned row_count() const { return m_rows.size(); }

    unsigned column_count() const { return m_columns.size(); }
    template <typename L>
    L dot_product_with_row(unsigned row, const std::vector<L> & w) {
        L ret = zero_of_type<L>();
        lean_assert(row < m_rows.size());
        for (auto & it : m_rows[row]) {
            ret += w[it.m_j] * it.get_val();
        }
        return ret;
    };

    unsigned lowest_row_in_column(unsigned col) {
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

    T dot_product_with_column(const std::vector<T> & y, unsigned j) const {
        lean_assert(j < column_count());
        T ret = numeric_traits<T>::zero();
        for (auto & it : m_columns[j]) {
            ret += y[it.m_i] * it.m_value; // get_value_of_column_cell(it);
        }
        return ret;
    }

    void add_columns_at_the_end(unsigned delta) {
        for (unsigned i = 0; i < delta; i++)
            add_column();
    }

    void add_column() {
        m_columns.push_back(column_strip());
    }

    void forget_last_columns(unsigned how_many_to_forget) {
        lean_assert(m_columns.size() >= how_many_to_forget);
        unsigned j = column_count() - 1;
        for (; how_many_to_forget > 0; how_many_to_forget--) {
            remove_last_column(j --);
        }
    }

    void remove_last_column(unsigned j) {
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

    void scale_row(unsigned row, T const & alpha) {
        for (auto & t : m_rows[row]) {
            t.set_val(t.get_val() * alpha);
            m_columns[t.m_j][t.m_offset].m_value *= alpha;
        }
    }

    void divide_row_by_constant(unsigned row, T const & alpha) {
        for (auto & t : m_rows[row]) {
            t.set_val(t.get_val() / alpha);
            m_columns[t.m_j][t.m_offset].m_value /= alpha;
        }
    }

    void scale_column(unsigned column, T const & alpha) {
        for (auto & t : m_columns[column]) {
            t.m_value *= alpha;
            auto & r = m_rows[t.m_i][t.m_offset];
            r.set_val(r.get_val() *= alpha);
        }
    }

#ifdef LEAN_DEBUG
    void regen_domain() {
        m_domain.clear();
        for (int i = 0; i < m_rows.size(); i++){
            for (auto & t : m_rows[i]) {
                m_domain.insert(std::make_pair(i, t.m_j));
            }
        }
    }
#endif

    // offs - offset in columns
    row_cell<T> make_row_cell(unsigned row, unsigned offs, T const & val) {
        row_cell<T> r(row, offs, val);
        return r;
    }

    column_cell<T> make_column_cell(unsigned column, unsigned offset, T const & val) {
        column_cell<T> r(column, offset, val);
        return r;
    }

    void set(unsigned row, unsigned col, T const & val) {
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

    ref operator()(unsigned row, unsigned col) { return ref(*this, row, col); }

    std::set<pair<unsigned, unsigned>>  get_domain() {
        std::set<pair<unsigned, unsigned>> ret;
        for (unsigned i = 0; i < m_rows.size(); i++) {
            for (auto it : m_rows[i]) {
                ret.insert(std::make_pair(i, it.m_j));
            }
        }
        return ret;
    }


    void copy_column_to_vector (unsigned j, indexed_vector<T> & v) const {
        lean_assert(j < m_columns.size());
        for (auto & it : m_columns[j]) {
            if (!is_zero(it.m_value))
                 v.set_value(it.m_value, it.m_i);
        }
    }
    void copy_column_to_vector (unsigned j, std::vector<T> & v) const {
        v.resize(row_count(), numeric_traits<T>::zero());
        for (auto & it : m_columns[j]) {
            if (!is_zero(it.m_value))
                v[it.m_i]=it.m_value;
        }
    }

    void add_column_to_vector (const T & a, unsigned j, T * v) const {
        for (auto & it : m_columns[j]) {
            v[it.m_i] += a * it.m_value;
        }
    }

    T get_max_abs_in_row(unsigned row) const {
        T ret = numeric_traits<T>::zero();
        for (auto & t : m_rows[row]) {
            T a = abs(t.get_val());
            if (a  > ret) {
                ret = a;
            }
        }
        return ret;
    }

    T get_min_abs_in_row(unsigned row) const {
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


    T get_max_abs_in_column(unsigned column) const {
        T ret = numeric_traits<T>::zero();
        for (auto & t : m_columns[column]) {
            T a = abs(t.m_value);
            if (a  > ret) {
                ret = a;
            }
        }
        return ret;
    }

     T get_min_abs_in_column(unsigned column) const {
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
    void check_consistency() {
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


    void cross_out_row(unsigned k) {
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

    //
    void fix_row_indices_in_each_column_for_crossed_row(unsigned k) {
        for (unsigned j = 0; j < m_columns.size(); j++) {
            auto & col = m_columns[j];
            for (int i = 0; i < col.size(); i++) {
                if (col[i].m_i > k) {
                    col[i].m_i--;
                }
            }
        }
    }

    void cross_out_row_from_columns(unsigned k, row_strip & row) {
        for (auto & t : row) {
            cross_out_row_from_column(t.m_j, k);
        }
    }

    void cross_out_row_from_column(unsigned col, unsigned k) {
        auto & s = m_columns[col];
        for (unsigned i = 0; i < s.size(); i++) {
            if (s[i].m_i == k) {
                s.erase(s.begin() + i);
                break;
            }
        }
    }

    T get_elem(unsigned i, unsigned j) const { // should not be used in efficient code !!!!
        for (auto & t : m_rows[i]) {
            if (t.m_j == j) {
                return t.get_val();
            }
        }
        return numeric_traits<T>::zero();
    }


    unsigned number_of_non_zeroes_in_column(unsigned j) const {
        return m_columns[j].size();
    }

    unsigned number_of_non_zeroes_in_row(unsigned i) const {
        return m_rows[i].number_of_non_zeros();
    }

    void scan_row_to_work_vector(unsigned i) {
        for (auto & rc : m_rows[i]) {
            m_work_pivot_vector[rc.m_j] = rc.get_val();
        }
    }

    void clean_row_work_vector(unsigned i) {
        for (auto & rc : m_rows[i]) {
            m_work_pivot_vector[rc.m_j] = numeric_traits<T>::zero();
        }
    }


#ifdef LEAN_DEBUG
    unsigned get_number_of_rows() const { return row_count(); }
    unsigned get_number_of_columns() const { return column_count(); }
    virtual void set_number_of_rows(unsigned /*m*/) { }
    virtual void set_number_of_columns(unsigned /*n*/) { }
#endif
    // const T & get_value_of_column_cell(column_cell<T> const & cc) const {
    //     lean_assert(cc.m_i < m_rows.size());
    //     lean_assert(cc.m_offset < m_rows[cc.m_i].size());
    //     return m_rows[cc.m_i][cc.m_offset].get_val();
    // }

    T get_max_val_in_row(unsigned i) const {
        lean_assert(false);
        throw 0;// not implemented
    }

    T get_balance() const {
        T ret = zero_of_type<T>();
        for (unsigned i = 0; i < row_count();  i++) {
            ret += get_row_balance(i);
        }
        return ret;
    }

    T get_row_balance(unsigned row) const {
        T ret = zero_of_type<T>();
        for (auto & t : m_rows[row]) {
            if (numeric_traits<T>::is_zero(t.get_val())) continue;
            T a = abs(t.get_val());
            numeric_traits<T>::log(a);
            ret += a * a;
        }
        return ret;
    }
    bool col_val_equal_to_row_val() const {
        for (auto & r : m_rows) {
            for (auto & rc : r) {
                lean_assert(rc.get_val() == m_columns[rc.m_j][rc.m_offset].m_value);
            }
        }
        return true;
    }
};
}
