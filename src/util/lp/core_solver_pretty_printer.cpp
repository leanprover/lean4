/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <limits>
#include <string>
#include <algorithm>
#include "util/lp/lp_core_solver_base.h"
#include "util/lp/core_solver_pretty_printer.h"
namespace lean {


template <typename T, typename X>
core_solver_pretty_printer<T, X>::core_solver_pretty_printer(lp_core_solver_base<T, X > & core_solver, std::ostream & out):
    m_out(out),
    m_core_solver(core_solver),
    m_column_widths(core_solver.m_A.column_count(), 0),
    m_A(core_solver.m_A.row_count(), vector<string>(core_solver.m_A.column_count(), "")),
    m_signs(core_solver.m_A.row_count(), vector<string>(core_solver.m_A.column_count(), " ")),
    m_costs(ncols(), ""),
    m_cost_signs(ncols(), " "),
    m_rs(ncols(), zero_of_type<X>()) {
    m_w_buff = new T[m_core_solver.m_m];
    m_ed_buff = new T[m_core_solver.m_m];
    m_core_solver.save_state(m_w_buff, m_ed_buff);
    init_m_A_and_signs();
    init_costs();
    init_column_widths();
    init_rs_width();
    m_cost_title = "costs";
    m_basis_heading_title = "heading";
    m_x_title = "x*";
    m_title_width = std::max(std::max(m_cost_title.size(), std::max(m_basis_heading_title.size(), m_x_title.size())), m_approx_norm_title.size());
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_costs() {
    vector<T> local_y(m_core_solver.m_m);
    m_core_solver.solve_yB(local_y);
    for (unsigned i = 0; i < ncols(); i++) {
        if (m_core_solver.m_basis_heading[i] < 0) {
            T t = m_core_solver.m_costs[i] - m_core_solver.m_A.dot_product_with_column(local_y, i);
            set_coeff(m_costs, m_cost_signs, i, t, m_core_solver.column_name(i));
        }
    }
}

template <typename T, typename X> core_solver_pretty_printer<T, X>::~core_solver_pretty_printer() {
    m_core_solver.restore_state(m_w_buff, m_ed_buff);
    delete [] m_w_buff;
    delete [] m_ed_buff;
}
template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_rs_width() {
    m_rs_width = T_to_string(m_core_solver.get_cost()).size();
    for (unsigned i = 0; i < nrows(); i++) {
        auto wt = T_to_string(m_rs[i]).size();
        if (wt > m_rs_width) {
            m_rs_width = wt;
        }
    }
}

template <typename T, typename X> T core_solver_pretty_printer<T, X>::current_column_norm() {
    T ret = zero_of_type<T>();
    for (T & ed : m_core_solver.m_ed)
        ret += ed * ed;
    return ret;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_m_A_and_signs() {
    for (unsigned column = 0; column < ncols(); column++) {
        m_core_solver.solve_Bd(column); // puts the result into m_core_solver.m_ed
        string name = m_core_solver.column_name(column);
        for (unsigned row = 0; row < nrows(); row ++) {
            set_coeff(
                      m_A[row],
                      m_signs[row],
                      column,
                      m_core_solver.m_ed[row],
                      name);
            m_rs[row] += m_core_solver.m_ed[row] * m_core_solver.m_x[column];
        }
        m_exact_column_norms.push_back(current_column_norm() + 1);
    }
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::init_column_widths() {
    for (unsigned i = 0; i < ncols(); i++) {
        m_column_widths[i] = get_column_width(i);
    }
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::adjust_width_with_low_bound(unsigned column, unsigned & w) {
    if (!m_core_solver.low_bounds_are_set()) return;
    w = std::max(w, (unsigned)T_to_string(m_core_solver.low_bound_value(column)).size());
}
template <typename T, typename X> void core_solver_pretty_printer<T, X>::adjust_width_with_upper_bound(unsigned column, unsigned & w) {
    w = std::max(w, (unsigned)T_to_string(m_core_solver.upper_bound_value(column)).size());
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::adjust_width_with_bounds(unsigned column, unsigned & w) {
    switch (m_core_solver.get_column_type(column)) {
    case fixed:
    case boxed:
        adjust_width_with_low_bound(column, w);
        adjust_width_with_upper_bound(column, w);
        break;
    case low_bound:
        adjust_width_with_low_bound(column, w);
        break;
    case upper_bound:
        adjust_width_with_upper_bound(column, w);
        break;
    case free_column:
        break;
    default:
        lean_assert(false);
        break;
    }
}


template <typename T, typename X> unsigned core_solver_pretty_printer<T, X>:: get_column_width(unsigned column) {
    unsigned w = std::max(m_costs[column].size(), T_to_string(m_core_solver.m_x[column]).size());
    adjust_width_with_bounds(column, w);
    adjust_width_with_basis_heading(column, w);
    for (unsigned i = 0; i < nrows(); i++) {
        unsigned cellw =  m_A[i][column].size();
        if (cellw > w) {
            w = cellw;
        }
    }
    w = std::max(w, (unsigned)T_to_string(m_exact_column_norms[column]).size());
    w = std::max(w, (unsigned)T_to_string(m_core_solver.m_column_norms[column]).size());
    return w;
}

template <typename T, typename X> std::string core_solver_pretty_printer<T, X>::regular_cell_string(unsigned row, unsigned /* column */, std::string name) {
    T t = fabs(m_core_solver.m_ed[row]);
    if ( t == 1) return name;
    return T_to_string(t) + name;
}


template <typename T, typename X> void core_solver_pretty_printer<T, X>::set_coeff(vector<string>& row, vector<string> & row_signs, unsigned col, const T & t, string name) {
    if (numeric_traits<T>::is_zero(t)) {
        return;
    }
    if (col > 0) {
        if (t > 0) {
            row_signs[col] = "+";
            row[col] = t != 1? T_to_string(t) + name : name;
        } else {
            row_signs[col] = "-";
            row[col] = t != -1? T_to_string(-t) + name: name;
        }
    } else { // col == 0
        if (t == -1) {
            row[col] = "-" + name;
        } else if (t == 1) {
            row[col] = name;
        } else {
            row[col] = T_to_string(t) + name;
        }
    }
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_x() {
    if (ncols() == 0) {
        return;
    }

    int blanks = m_title_width + 1 - m_x_title.size();
    m_out << m_x_title;
    print_blanks(blanks, m_out);

    auto bh = m_core_solver.m_x;
    for (unsigned i = 0; i < ncols(); i++) {
        string s = T_to_string(bh[i]);
        int blanks = m_column_widths[i] - s.size();
        print_blanks(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> std::string core_solver_pretty_printer<T, X>::get_low_bound_string(unsigned j) {
    switch (m_core_solver.get_column_type(j)){
    case boxed:
    case low_bound:
    case fixed:
        if (m_core_solver.low_bounds_are_set())
            return T_to_string(m_core_solver.low_bound_value(j));
        else
            return std::string("0");
        break;
    default:
        return std::string();
    }
}

template <typename T, typename X> std::string core_solver_pretty_printer<T, X>::get_upp_bound_string(unsigned j) {
    switch (m_core_solver.get_column_type(j)){
    case boxed:
    case upper_bound:
    case fixed:
        return T_to_string(m_core_solver.upper_bound_value(j));
        break;
    default:
        return std::string();
    }
}


template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_lows() {
    if (ncols() == 0) {
        return;
    }
    int blanks = m_title_width + 1 - m_low_bounds_title.size();
    m_out << m_low_bounds_title;
    print_blanks(blanks, m_out);

    for (unsigned i = 0; i < ncols(); i++) {
        string s = get_low_bound_string(i);
        int blanks = m_column_widths[i] - s.size();
        print_blanks(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_upps() {
    if (ncols() == 0) {
        return;
    }
    int blanks = m_title_width + 1 - m_upp_bounds_title.size();
    m_out << m_upp_bounds_title;
    print_blanks(blanks, m_out);

    for (unsigned i = 0; i < ncols(); i++) {
        string s = get_upp_bound_string(i);
        int blanks = m_column_widths[i] - s.size();
        print_blanks(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_exact_norms() {
    int blanks = m_title_width + 1 - m_exact_norm_title.size();
    m_out << m_exact_norm_title;
    print_blanks(blanks, m_out);
    for (unsigned i = 0; i < ncols(); i++) {
        string s = get_exact_column_norm_string(i);
        int blanks = m_column_widths[i] - s.size();
        print_blanks(blanks, m_out);
        m_out << s << "   ";
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_approx_norms() {
    int blanks = m_title_width + 1 - m_approx_norm_title.size();
    m_out << m_approx_norm_title;
    print_blanks(blanks, m_out);
    for (unsigned i = 0; i < ncols(); i++) {
        string s = T_to_string(m_core_solver.m_column_norms[i]);
        int blanks = m_column_widths[i] - s.size();
        print_blanks(blanks, m_out);
        m_out << s << "   ";
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print() {
    for (unsigned i = 0; i < nrows(); i++) {
        print_row(i);
    }
    print_bottom_line();
    print_cost();
    print_x();
    print_basis_heading();
    print_lows();
    print_upps();
    print_exact_norms();
    print_approx_norms();
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_basis_heading() {
    int blanks = m_title_width + 1 - m_basis_heading_title.size();
    m_out << m_basis_heading_title;
    print_blanks(blanks, m_out);

    if (ncols() == 0) {
        return;
    }
    auto bh = m_core_solver.m_basis_heading;
    for (unsigned i = 0; i < ncols(); i++) {
        string s = T_to_string(bh[i]);
        int blanks = m_column_widths[i] - s.size();
        print_blanks(blanks, m_out);
        m_out << s << "   "; // the column interval
    }
    m_out << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_cost() {
    int blanks = m_title_width + 1 - m_cost_title.size();
    m_out << m_cost_title;
    print_blanks(blanks, m_out);
    print_given_rows(m_costs, m_cost_signs, m_core_solver.get_cost());
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_given_rows(vector<string> & row, vector<string> & signs, X rst) {
    for (unsigned col = 0; col < row.size(); col++) {
        unsigned width = m_column_widths[col];
        string s = row[col];
        int number_of_blanks = width - s.size();
        lean_assert(number_of_blanks >= 0);
        print_blanks(number_of_blanks, m_out);
        m_out << s << ' ';
        if (col < row.size() - 1) {
            m_out << signs[col + 1] << ' ';
        }
    }
    m_out << '=';

    string rs = T_to_string(rst);
    int nb = m_rs_width - rs.size();
    lean_assert(nb >= 0);
    print_blanks(nb + 1, m_out);
    m_out << rs << std::endl;
}

template <typename T, typename X> void core_solver_pretty_printer<T, X>::print_row(unsigned i){
    print_blanks(m_title_width + 1, m_out);
    auto row = m_A[i];
    auto sign_row = m_signs[i];
    auto rs = m_rs[i];
    print_given_rows(row, sign_row, rs);
}
}
