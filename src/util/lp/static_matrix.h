/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <set>
#include <unordered_map>
#include <utility>
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include "util/lp/sparse_vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/permutation_matrix.h"
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
    void set_val(T v) { m_value = v;  }
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
    void init_row_columns(unsigned m, unsigned n);

        // constructor with no parameters
    static_matrix() {}

    // constructor
    static_matrix(unsigned m, unsigned n): m_work_pivot_vector(m, numeric_traits<T>::zero())  {
        init_row_columns(m, n);
    }
    // constructor that copies columns of the basis from A
    static_matrix(static_matrix const &A, unsigned * basis);

    void clear();

    void init_work_pivot_vector(unsigned m);

    void init_empty_matrix(unsigned m, unsigned n);

    unsigned row_count() const { return m_rows.size(); }

    unsigned column_count() const { return m_columns.size(); }
    template <typename L>
    L dot_product_with_row(unsigned row, const std::vector<L> & w);;

    unsigned lowest_row_in_column(unsigned col);

    T dot_product_with_column(const std::vector<T> & y, unsigned j) const;

    void add_columns_at_the_end(unsigned delta);

    void add_column() {m_columns.push_back(column_strip()); }

    void forget_last_columns(unsigned how_many_to_forget);

    void remove_last_column(unsigned j);

    void scale_row(unsigned row, T const & alpha);

    void divide_row_by_constant(unsigned row, T const & alpha);

    void scale_column(unsigned column, T const & alpha);

#ifdef LEAN_DEBUG
    void regen_domain();
#endif

    // offs - offset in columns
    row_cell<T> make_row_cell(unsigned row, unsigned offs, T const & val) {
        return row_cell<T>(row, offs, val);
    }

    column_cell<T> make_column_cell(unsigned column, unsigned offset, T const & val) {
        return column_cell<T>(column, offset, val);
    }

    void set(unsigned row, unsigned col, T const & val);

    ref operator()(unsigned row, unsigned col) { return ref(*this, row, col); }

    std::set<pair<unsigned, unsigned>>  get_domain();

    void copy_column_to_vector (unsigned j, indexed_vector<T> & v) const;

    void copy_column_to_vector (unsigned j, std::vector<T> & v) const;

    void add_column_to_vector (const T & a, unsigned j, T * v) const;
    T get_max_abs_in_row(unsigned row) const;

    T get_min_abs_in_row(unsigned row) const;
    T get_max_abs_in_column(unsigned column) const;

    T get_min_abs_in_column(unsigned column) const;

#ifdef LEAN_DEBUG
    void check_consistency();
#endif


    void cross_out_row(unsigned k);

    //
    void fix_row_indices_in_each_column_for_crossed_row(unsigned k);

    void cross_out_row_from_columns(unsigned k, row_strip & row);

    void cross_out_row_from_column(unsigned col, unsigned k);

    T get_elem(unsigned i, unsigned j) const;


    unsigned number_of_non_zeroes_in_column(unsigned j) const { return m_columns[j].size(); }

    unsigned number_of_non_zeroes_in_row(unsigned i) const { return m_rows[i].number_of_non_zeros(); }

    void scan_row_to_work_vector(unsigned i);

    void clean_row_work_vector(unsigned i);


#ifdef LEAN_DEBUG
    unsigned get_number_of_rows() const { return row_count(); }
    unsigned get_number_of_columns() const { return column_count(); }
    virtual void set_number_of_rows(unsigned /*m*/) { }
    virtual void set_number_of_columns(unsigned /*n*/) { }
#endif

    T get_max_val_in_row(unsigned /* i */) const { lean_unreachable();   }

    T get_balance() const;

    T get_row_balance(unsigned row) const;

    bool col_val_equal_to_row_val() const;
};
}
