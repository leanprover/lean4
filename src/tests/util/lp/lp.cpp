/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Lev Nachmanson
*/
#include <limits>
#include <dirent.h>
#include <algorithm>
#include <string>
#include <set>
#include <iostream>
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <ctime>
#include <vector>
#include <stdlib.h>
#include <utility>
#include "util/pair.h"
#include "util/lp/lp_primal_simplex.h"
#include "tests/util/lp/mps_reader.h"
#include "tests/util/lp/smt_reader.h"
#include "util/numerics/mpq.h"
#include "util/lp/binary_heap_priority_queue.h"
#include "tests/util/lp/argument_parser.h"
#include "tests/util/lp/test_file_reader.h"
#include "util/lp/indexed_value.h"
#include "tests/util/lp/init_module.h"
#include "util/numerics/init_module.h"
#include "util/lp/lar_solver.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/binary_heap_upair_queue.h"
using namespace lean;
unsigned seed = 1;
#ifdef LEAN_DEBUG
unsigned lp_settings::ddd = 0;
#endif
std::unordered_map<unsigned, std::string> default_column_names(unsigned n) {
    std::unordered_map<unsigned, std::string> ret;
    for (unsigned i = 0; i < n; i++) {
        ret[i] = std::string("x") + T_to_string(i);
    }
    return ret;
}

template <typename T, typename X>
void test_matrix(sparse_matrix<T, X> & a) {
    auto m = a.dimension();

// copy a to b in the reversed order
    sparse_matrix<T, X> b(m);
    std::cout << "copy b to a"<< std::endl;
    for (int row = m - 1; row >= 0; row--)
        for (int col = m - 1; col >= 0; col --) {
            b(row, col) = (T const&) a(row, col);
        }


    std::cout << "zeroing b in the reverse order"<< std::endl;
    for (int row = m - 1; row >= 0; row--)
        for (int col = m - 1; col >= 0; col --)
            b.set(row, col, T(0));



    for (unsigned row = 0; row < m; row ++)
        for (unsigned col = 0; col < m; col ++)
            a.set(row, col, T(0));


    unsigned i = my_random() % m;
    unsigned j = my_random() % m;

    auto t = T(1);

    a.set(i, j, t);

    lean_assert(a.get(i, j) == t);

    unsigned j1;
    if (j < m - 1) {
        j1 = m - 1;
        a.set(i, j1, T(2));
    }
}

void tst1() {
    std::cout << "testing the minimial matrix with 1 row and 1 column" << std::endl;
    sparse_matrix<float, float> m0(1);
    m0.set(0, 0, 1);
    // print_matrix(m0);
    m0.set(0, 0, 0);
    // print_matrix(m0);
    test_matrix(m0);

    unsigned rows = 2;
    sparse_matrix<float, float> m(rows);
    std::cout << "setting m(0,1)=" << std::endl;

    m.set(0, 1,  11);
    m.set(0, 0,  12);

    // print_matrix<float>(m);

    test_matrix(m);

    sparse_matrix<float, float> m1(2);
    m1.set(0, 0, 2);
    m1.set(1, 0, 3);
    // print_matrix(m1);
    std::cout << " zeroing matrix 2 by 2" << std::endl;
    m1.set(0, 0, 0);
    m1.set(1, 0, 0);
    // print_matrix(m1);

    test_matrix(m1);


    std::cout << "printing zero matrix 3 by 1" << std::endl;
    sparse_matrix<float, float> m2(3);
    // print_matrix(m2);

    m2.set(0, 0, 1);
    m2.set(2, 0, 2);
    std::cout << "printing  matrix 3 by 1 with a gap" << std::endl;
    // print_matrix(m2);

    test_matrix(m2);

    sparse_matrix<float, float> m10by9(10);
    m10by9.set(0, 1, 1);

    m10by9(0, 1) = 4;

    float test = m10by9(0, 1);

    std::cout << "got " << test << std::endl;


    m10by9.set(0, 8, 8);
    m10by9.set(3, 4, 7);
    m10by9.set(3, 2, 5);
    m10by9.set(3, 8, 99);
    m10by9.set(3, 2, 6);
    m10by9.set(1, 8, 9);
    m10by9.set(4, 0, 40);
    m10by9.set(0, 0, 10);

    std::cout << "printing  matrix 10 by 9" << std::endl;
    // print_matrix(m10by9);


    test_matrix(m10by9);
    std::cout <<"zeroing m10by9\n";
#ifdef LEAN_DEBUG
    for (unsigned int i = 0; i < m10by9.dimension(); i++)
        for (unsigned int j = 0; j < m10by9.column_count(); j++)
            m10by9.set(i, j, 0);
#endif
    // print_matrix(m10by9);
}

vector<int> allocate_basis_heading(unsigned count) { // the rest of initilization will be handled by lu_QR
    vector<int> basis_heading(count, -1);
    return basis_heading;
}


void test_small_lu(lp_settings & settings) {
    std::cout << " test_small_lu" << std::endl;
    static_matrix<double, double> m(3, 6);
    vector<unsigned> basis(3);
    basis[0] = 0;
    basis[1] = 1;
    basis[2] = 3;

    m(0, 0) = 1; m(0, 2)= 3.9; m(2, 3) = 11; m(0, 5) = -3;
    m(1, 1) = 4; m(1, 4) = 7;
    m(2, 0) = 1.8; m(2, 2) = 5; m(2, 4) = 2; m(2, 5) = 8;

#ifdef LEAN_DEBUG
    print_matrix(m, std::cout);
#endif
    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, m.row_count(), heading, m.column_count(), non_basic_columns);
    lu<double, double> l(m, basis, heading, settings, non_basic_columns);
    lean_assert(l.is_correct());
    indexed_vector<double> w(m.row_count());
    cout << "entering 2, leaving 0" << std::endl;
    l.prepare_entering(2, w); // to init vector w
    l.replace_column(0, 0, w);
    l.change_basis(2, 0);
    // #ifdef LEAN_DEBUG
    // cout << "we were factoring " << std::endl;
    // print_matrix(get_B(l));
    // #endif
    lean_assert(l.is_correct());
    cout << "entering 4, leaving 3" << std::endl;
    l.prepare_entering(4, w); // to init vector w
    l.replace_column(3, 0, w);
    l.change_basis(4, 3);
    cout << "we were factoring " << std::endl;
#ifdef LEAN_DEBUG
    print_matrix(get_B(l), std::cout);
#endif
    lean_assert(l.is_correct());

    cout << "entering 5, leaving 1" << std::endl;
    l.prepare_entering(5, w); // to init vector w
    l.replace_column(1, 0, w);
    l.change_basis(5, 1);
    cout << "we were factoring " << std::endl;
#ifdef LEAN_DEBUG
    print_matrix(get_B(l), std::cout);
#endif
    lean_assert(l.is_correct());
    cout << "entering 3, leaving 2" << std::endl;
    l.prepare_entering(3, w); // to init vector w
    l.replace_column(2, 0, w);
    l.change_basis(3, 2);
    cout << "we were factoring " << std::endl;
#ifdef LEAN_DEBUG
    print_matrix(get_B(l), std::cout);
#endif
    lean_assert(l.is_correct());
}



void fill_long_row(sparse_matrix<double, double> &m, int i) {
    int n = m.dimension();
    for (int j = 0; j < n; j ++) {
        m (i, (j + i) % n) = j * j;
    }
}

void fill_long_row(static_matrix<double, double> &m, int i) {
    int n = m.column_count();
    for (int j = 0; j < n; j ++) {
        m (i, (j + i) % n) = j * j;
    }
}


void fill_long_row_exp(sparse_matrix<double, double> &m, int i) {
    int n = m.dimension();

    for (int j = 0; j < n; j ++) {
        m(i, j) = my_random() % 20;
    }
}

void fill_long_row_exp(static_matrix<double, double> &m, int i) {
    int n = m.column_count();

    for (int j = 0; j < n; j ++) {
        m(i, j) = my_random() % 20;
    }
}

void fill_larger_sparse_matrix_exp(sparse_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.dimension(); i++ )
        fill_long_row_exp(m, i);
}

void fill_larger_sparse_matrix_exp(static_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.row_count(); i++ )
        fill_long_row_exp(m, i);
}


void fill_larger_sparse_matrix(sparse_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.dimension(); i++ )
        fill_long_row(m, i);
}

void fill_larger_sparse_matrix(static_matrix<double, double> & m){
    for ( unsigned i = 0; i < m.row_count(); i++ )
        fill_long_row(m, i);
}


int perm_id = 0;

#ifdef LEAN_DEBUG
void test_larger_lu_exp(lp_settings & settings) {
    std::cout << " test_larger_lu_exp" << std::endl;
    static_matrix<double, double> m(6, 12);
    std::vector<unsigned> basis(6);
    basis[0] = 1;
    basis[1] = 3;
    basis[2] = 0;
    basis[3] = 4;
    basis[4] = 5;
    basis[5] = 6;


    fill_larger_sparse_matrix_exp(m);
    // print_matrix(m);
    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, m.row_count(), heading, m.column_count(), non_basic_columns);
    lu<double, double> l(m, basis, heading, settings, non_basic_columns);

    dense_matrix<double, double> left_side = l.get_left_side();
    dense_matrix<double, double> right_side = l.get_right_side();
    lean_assert(left_side == right_side);
    int leaving = 3;
    int entering = 8;
    for (unsigned i = 0; i < m.row_count(); i++) {
        std::cout << static_cast<double>(m(i, entering)) << std::endl;
    }

    indexed_vector<double> w(m.row_count());

    l.prepare_entering(entering, w);
    l.replace_column(leaving, 0, w);
    l.change_basis(entering, leaving);
    lean_assert(l.is_correct());

    l.prepare_entering(11, w); // to init vector w
    l.replace_column(0, 0, w);
    l.change_basis(11, 0);
    lean_assert(l.is_correct());
}

void test_larger_lu_with_holes(lp_settings & settings) {
    std::cout << " test_larger_lu_with_holes" << std::endl;
    static_matrix<double, double> m(8, 9);
    std::vector<unsigned> basis(8);
    for (unsigned i = 0; i < m.row_count(); i++) {
        basis[i] = i;
    }
    m(0, 0) = 1; m(0, 1) = 2; m(0, 2) = 3; m(0, 3) = 4; m(0, 4) = 5; m(0, 8) = 99;
    /*        */ m(1, 1) =- 6; m(1, 2) = 7; m(1, 3) = 8; m(1, 4) = 9;
    /*                     */ m(2, 2) = 10;
    /*                     */ m(3, 2) = 11; m(3, 3) = -12;
    /*                     */ m(4, 2) = 13; m(4, 3) = 14; m(4, 4) = 15;
    // the rest of the matrix is denser
    m(5, 4) = 28; m(5, 5) = -18; m(5, 6) = 19; m(5, 7) = 25;
    /*        */  m(6, 5) = 20; m(6, 6) = -21;
    /*        */  m(7, 5) = 22; m(7, 6) = 23; m(7, 7) = 24; m(7, 8) = 88;
    print_matrix(m, std::cout);
    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, m.row_count(), heading, m.column_count(), non_basic_columns);
    lu<double, double> l(m, basis, heading, settings, non_basic_columns);
    std::cout << "printing factorization" << std::endl;
    for (int i = l.tail_size() - 1; i >=0; i--) {
        auto lp = l.get_lp_matrix(i);
        lp->set_number_of_columns(m.row_count());
        lp->set_number_of_rows(m.row_count());
        print_matrix(* lp, std::cout);
    }

    dense_matrix<double, double> left_side = l.get_left_side();
    dense_matrix<double, double> right_side = l.get_right_side();
    if (!(left_side == right_side)) {
        std::cout << "different sides" << std::endl;
    }

    indexed_vector<double> w(m.row_count());
    l.prepare_entering(8, w); // to init vector w
    l.replace_column(0, 0, w);
    l.change_basis(8, 0);
    lean_assert(l.is_correct());
}


void test_larger_lu(lp_settings& settings) {
    std::cout << " test_larger_lu" << std::endl;
    static_matrix<double, double> m(6, 12);
    std::vector<unsigned> basis(6);
    basis[0] = 1;
    basis[1] = 3;
    basis[2] = 0;
    basis[3] = 4;
    basis[4] = 5;
    basis[5] = 6;


    fill_larger_sparse_matrix(m);
    print_matrix(m, std::cout);

    vector<int> heading = allocate_basis_heading(m.column_count());
    vector<unsigned> non_basic_columns;
    init_basis_heading_and_non_basic_columns_vector(basis, m.row_count(), heading, m.column_count(), non_basic_columns);
    auto l = lu<double, double> (m, basis, heading, settings, non_basic_columns);
    // std::cout << "printing factorization" << std::endl;
    // for (int i = lu.tail_size() - 1; i >=0; i--) {
    //     auto lp = lu.get_lp_matrix(i);
    //     lp->set_number_of_columns(m.row_count());
    //     lp->set_number_of_rows(m.row_count());
    //     print_matrix(* lp);
    // }

    dense_matrix<double, double> left_side = l.get_left_side();
    dense_matrix<double, double> right_side = l.get_right_side();
    if (!(left_side == right_side)) {
        cout << "left side" << std::endl;
        print_matrix(left_side, std::cout);
        cout << "right side" << std::endl;
        print_matrix(right_side, std::cout);

        std::cout << "different sides" << std::endl;
        cout << "initial factorization is incorrect" << std::endl;
        exit(1);
    }
    indexed_vector<double> w(m.row_count());
    l.prepare_entering(9, w); // to init vector w
    l.replace_column(0, 0, w);
    l.change_basis(9, 0);
    lean_assert(l.is_correct());
}


void test_lu(lp_settings & settings) {
    test_small_lu(settings);
    test_larger_lu(settings);
    test_larger_lu_with_holes(settings);
    test_larger_lu_exp(settings);
}
#endif






void init_b(std::vector<double> & b, sparse_matrix<double, double> & m, vector<double>& x) {
    for (unsigned i = 0; i < m.dimension(); i++) {
        b.push_back(m.dot_product_with_row(i, x));
    }
}

void init_b(std::vector<double> & b, static_matrix<double, double> & m, std::vector<double> & x) {
    for (unsigned i = 0; i < m.row_count(); i++) {
        b.push_back(m.dot_product_with_row(i, x));
    }
}


void test_lp_0() {
    std::cout << " test_lp_0 " << std::endl;
    static_matrix<double, double> m_(3, 7);
    m_(0, 0) = 3; m_(0, 1) = 2; m_(0, 2) = 1; m_(0, 3) = 2; m_(0, 4) = 1;
    m_(1, 0) = 1; m_(1, 1) = 1; m_(1, 2) = 1; m_(1, 3) = 1; m_(1, 5) = 1;
    m_(2, 0) = 4; m_(2, 1) = 3; m_(2, 2) = 3; m_(2, 3) = 4; m_(2, 6) = 1;
    std::vector<double> x_star(7);
    x_star[0] = 225; x_star[1] = 117; x_star[2] = 420;
    x_star[3] = x_star[4] = x_star[5] = x_star[6] = 0;
    std::vector<double> b;
    init_b(b, m_, x_star);
    std::vector<unsigned> basis(3);
    basis[0] = 0; basis[1] = 1; basis[2] = 2;
    std::vector<double> costs(7);
    costs[0] = 19;
    costs[1] = 13;
    costs[2] = 12;
    costs[3] = 17;
    costs[4] = 0;
    costs[5] = 0;
    costs[6] = 0;

    std::vector<column_type> column_types(7, low_bound);
    std::vector<double>  upper_bound_values;
    lp_settings settings;
    auto cn = default_column_names(m_.column_count());
    lp_primal_core_solver<double, double> lpsolver(m_, b, x_star, basis, costs, column_types, upper_bound_values, settings, cn);

    lpsolver.solve();
}

void test_lp_1() {
    std::cout << " test_lp_1 " << std::endl;
    static_matrix<double, double> m(4, 7);
    m(0, 0) =  1;  m(0, 1) = 3;  m(0, 2) = 1;  m(0, 3) = 1;
    m(1, 0) = -1;                m(1, 2) = 3;  m(1, 4) = 1;
    m(2, 0) =  2;  m(2, 1) = -1; m(2, 2) = 2;  m(2, 5) = 1;
    m(3, 0) =  2;  m(3, 1) =  3; m(3, 2) = -1; m(3, 6) = 1;
#ifdef LEAN_DEBUG
    print_matrix(m, std::cout);
#endif
    std::vector<double> x_star(7);
    x_star[0] = 0; x_star[1] = 0; x_star[2] = 0;
    x_star[3] = 3; x_star[4] = 2; x_star[5] = 4; x_star[6] = 2;

    std::vector<unsigned> basis(4);
    basis[0] = 3; basis[1] = 4; basis[2] = 5; basis[3] = 6;

    std::vector<double> b;
    b.push_back(3);
    b.push_back(2);
    b.push_back(4);
    b.push_back(2);

    std::vector<double> costs(7);
    costs[0] = 5;
    costs[1] = 5;
    costs[2] = 3;
    costs[3] = 0;
    costs[4] = 0;
    costs[5] = 0;
    costs[6] = 0;



    std::vector<column_type> column_types(7, low_bound);
    std::vector<double>  upper_bound_values;

    std::cout << "calling lp\n";
    lp_settings settings;
    auto cn = default_column_names(m.column_count());

    lp_primal_core_solver<double, double> lpsolver(m, b,
                                    x_star,
                                    basis,
                                    costs,
                                    column_types, upper_bound_values, settings, cn);

    lpsolver.solve();
}


void test_lp_primal_core_solver() {
    test_lp_0();
    test_lp_1();
}


#ifdef LEAN_DEBUG
template <typename T, typename X>
void test_swap_rows_with_permutation(sparse_matrix<T, X>& m){
    cout << "testing swaps" << std::endl;
    unsigned dim = m.row_count();
    dense_matrix<double, double> original(m);
    permutation_matrix<double, double> q(dim);
    print_matrix(m, std::cout);
    lean_assert(original == q * m);
    for (int i = 0; i < 100; i++) {
        unsigned row1 = my_random() % dim;
        unsigned row2 = my_random() % dim;
        if (row1 == row2) continue;
        cout << "swap " << row1 << " " << row2 << std::endl;
        m.swap_rows(row1, row2);
        q.transpose_from_left(row1, row2);
        lean_assert(original == q * m);
        print_matrix(m, std::cout);
        cout << std::endl;
    }
}
#endif
template <typename T, typename X>
void fill_matrix(sparse_matrix<T, X>& m); // forward definition
#ifdef LEAN_DEBUG
template <typename T, typename X>
void test_swap_cols_with_permutation(sparse_matrix<T, X>& m){
    cout << "testing swaps" << std::endl;
    unsigned dim = m.row_count();
    dense_matrix<double, double> original(m);
    permutation_matrix<double, double> q(dim);
    print_matrix(m, std::cout);
    lean_assert(original == q * m);
    for (int i = 0; i < 100; i++) {
        unsigned row1 = my_random() % dim;
        unsigned row2 = my_random() % dim;
        if (row1 == row2) continue;
        cout << "swap " << row1 << " " << row2 << std::endl;
        m.swap_rows(row1, row2);
        q.transpose_from_right(row1, row2);
        lean_assert(original == q * m);
        print_matrix(m, std::cout);
        cout << std::endl;
    }
}


template <typename T, typename X>
void test_swap_rows(sparse_matrix<T, X>& m, unsigned i0, unsigned i1){
    std::cout << "test_swap_rows(" << i0 << "," << i1 << ")" << std::endl;
    sparse_matrix<T, X> mcopy(m.dimension());
    for (unsigned i = 0; i  < m.dimension(); i++)
        for (unsigned j = 0; j < m.dimension(); j++) {
            mcopy(i, j)= m(i, j);
    }
    std::cout << "swapping rows "<< i0 << "," << i1 << std::endl;
    m.swap_rows(i0, i1);

    for (unsigned j = 0; j < m.dimension(); j++) {
        lean_assert(mcopy(i0, j) == m(i1, j));
        lean_assert(mcopy(i1, j) == m(i0, j));
    }
}
template <typename T, typename X>
void test_swap_columns(sparse_matrix<T, X>& m, unsigned i0, unsigned i1){
    std::cout << "test_swap_columns(" << i0 << "," << i1 << ")" << std::endl;
    sparse_matrix<T, X> mcopy(m.dimension());
    for (unsigned i = 0; i  < m.dimension(); i++)
        for (unsigned j = 0; j < m.dimension(); j++) {
            mcopy(i, j)= m(i, j);
    }
    m.swap_columns(i0, i1);

    for (unsigned j = 0; j < m.dimension(); j++) {
        lean_assert(mcopy(j, i0) == m(j, i1));
        lean_assert(mcopy(j, i1) == m(j, i0));
    }

    for (unsigned i = 0; i  < m.dimension(); i++) {
        if (i == i0 || i == i1)
            continue;
        for (unsigned j = 0; j < m.dimension(); j++) {
            lean_assert(mcopy(j, i)== m(j, i));
        }
    }
}
#endif

template <typename T, typename X>
void fill_matrix(sparse_matrix<T, X>& m){
    int v = 0;
    for (int i = m.dimension() - 1; i >= 0; i--) {
        for (int j = m.dimension() - 1; j >=0; j--){
            m(i, j) = v++;
        }
    }
}

void test_pivot_like_swaps_and_pivot(){
    sparse_matrix<float, float> m(10);
    fill_matrix(m);
    // print_matrix(m);
// pivot at 2,7
    m.swap_columns(0, 7);
    // print_matrix(m);
    m.swap_rows(2, 0);
    // print_matrix(m);
    for (unsigned i = 1; i < m.dimension(); i++) {
        m(i, 0) = 0;
    }
    // print_matrix(m);

// say pivot at 3,4
    m.swap_columns(1, 4);
    // print_matrix(m);
    m.swap_rows(1, 3);
    // print_matrix(m);

    vector<float> row;
    float alpha = 2.33;
    unsigned pivot_row = 1;
    unsigned target_row = 2;
    unsigned pivot_row_0 = 3;
    float beta = 3.1;
    m(target_row, 3) = 0;
    m(target_row, 5) = 0;
    m(pivot_row, 6) = 0;
#ifdef LEAN_DEBUG
    print_matrix(m, std::cout);
#endif

    for (unsigned j = 0; j < m.dimension(); j++) {
        row.push_back(m(target_row, j) + alpha * m(pivot_row, j) + beta * m(pivot_row_0, j));
    }

    for (auto & t : row) {
        cout << t << ",";
    }
    cout << std::endl;
    lp_settings settings;
    m.pivot_row_to_row(pivot_row, alpha, target_row, settings);
    m.pivot_row_to_row(pivot_row_0, beta, target_row, settings);
    //  print_matrix(m);
    for (unsigned j = 0; j < m.dimension(); j++) {
        lean_assert(abs(row[j] - m(target_row, j)) < 0.00000001);
    }
}

#ifdef LEAN_DEBUG
void test_swap_rows() {
    sparse_matrix<float, float> m(10);
    fill_matrix(m);
    // print_matrix(m);
    test_swap_rows(m, 3, 5);

    test_swap_rows(m, 1, 3);


    test_swap_rows(m, 1, 3);

    test_swap_rows(m, 1, 7);

    test_swap_rows(m, 3, 7);

    test_swap_rows(m, 0, 7);

    m(0, 4) = 1;
    // print_matrix(m);
    test_swap_rows(m, 0, 7);

// go over some corner cases
    sparse_matrix<float, float> m0(2);
    test_swap_rows(m0, 0, 1);
    m0(0, 0) = 3;
    test_swap_rows(m0, 0, 1);
    m0(1, 0) = 3;
    test_swap_rows(m0, 0, 1);


    sparse_matrix<float, float> m1(10);
    test_swap_rows(m1, 0, 1);
    m1(0, 0) = 3;
    test_swap_rows(m1, 0, 1);
    m1(1, 0) = 3;
    m1(0, 3) = 5;
    m1(1, 3) = 4;
    m1(1, 8) = 8;
    m1(1, 9) = 8;

    test_swap_rows(m1, 0, 1);

    sparse_matrix<float, float> m2(3);
    test_swap_rows(m2, 0, 1);
    m2(0, 0) = 3;
    test_swap_rows(m2, 0, 1);
    m2(2, 0) = 3;
    test_swap_rows(m2, 0, 2);
}

void fill_uniformly(sparse_matrix<double, double> & m, unsigned dim) {
    int v = 0;
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            m(i, j) = v++;
        }
    }
}

void fill_uniformly(dense_matrix<double, double> & m, unsigned dim) {
    int v = 0;
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            m.set_elem(i, j, v++);
        }
    }
}

void sparse_matrix_with_permutaions_test() {
    unsigned dim = 4;
    sparse_matrix<double, double> m(dim);
    fill_uniformly(m, dim);
    dense_matrix<double, double> dm(dim, dim);
    fill_uniformly(dm, dim);
    dense_matrix<double, double> dm0(dim, dim);
    fill_uniformly(dm0, dim);
    permutation_matrix<double, double> q0(dim);
    q0[0] = 1;
    q0[1] = 0;
    q0[2] = 3;
    q0[3] = 2;
    permutation_matrix<double, double> q1(dim);
    q1[0] = 1;
    q1[1] = 2;
    q1[2] = 3;
    q1[3] = 0;
    permutation_matrix<double, double> p0(dim);
    p0[0] = 1;
    p0[1] = 0;
    p0[2] = 3;
    p0[3] = 2;
    permutation_matrix<double, double> p1(dim);
    p1[0] = 1;
    p1[1] = 2;
    p1[2] = 3;
    p1[3] = 0;

    m.multiply_from_left(q0);
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            lean_assert(m(i, j) == dm0.get_elem(q0[i], j));
        }
    }

    auto q0_dm = q0 * dm;
    lean_assert(m == q0_dm);

    m.multiply_from_left(q1);
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            lean_assert(m(i, j) == dm0.get_elem(q0[q1[i]], j));
        }
    }


    auto q1_q0_dm = q1 * q0_dm;

    lean_assert(m == q1_q0_dm);

    m.multiply_from_right(p0);

    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            lean_assert(m(i, j) == dm0.get_elem(q0[q1[i]], p0[j]));
        }
    }

    auto q1_q0_dm_p0 = q1_q0_dm * p0;

    lean_assert(m == q1_q0_dm_p0);

    m.multiply_from_right(p1);

    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            lean_assert(m(i, j) == dm0.get_elem(q0[q1[i]], p1[p0[j]]));
        }
    }

    auto q1_q0_dm_p0_p1 = q1_q0_dm_p0 * p1;
    lean_assert(m == q1_q0_dm_p0_p1);

    m.multiply_from_right(p1);
    for (unsigned i = 0; i < dim; i++) {
        for (unsigned j = 0; j < dim; j++) {
            lean_assert(m(i, j) == dm0.get_elem(q0[q1[i]], p1[p1[p0[j]]]));
        }
    }
    auto q1_q0_dm_p0_p1_p1 = q1_q0_dm_p0_p1 * p1;

    lean_assert(m == q1_q0_dm_p0_p1_p1);
}

void test_swap_columns() {
    sparse_matrix<float, float> m(10);
    fill_matrix(m);
    // print_matrix(m);

    test_swap_columns(m, 3, 5);

    test_swap_columns(m, 1, 3);

    test_swap_columns(m, 1, 3);

    // print_matrix(m);
    test_swap_columns(m, 1, 7);

    test_swap_columns(m, 3, 7);

    test_swap_columns(m, 0, 7);

    test_swap_columns(m, 0, 7);

// go over some corner cases
    sparse_matrix<float, float> m0(2);
    test_swap_columns(m0, 0, 1);
    m0(0, 0) = 3;
    test_swap_columns(m0, 0, 1);
    m0(0, 1) = 3;
    test_swap_columns(m0, 0, 1);


    sparse_matrix<float, float> m1(10);
    test_swap_columns(m1, 0, 1);
    m1(0, 0) = 3;
    test_swap_columns(m1, 0, 1);
    m1(0, 1) = 3;
    m1(3, 0) = 5;
    m1(3, 1) = 4;
    m1(8, 1) = 8;
    m1(9, 1) = 8;

    test_swap_columns(m1, 0, 1);

    sparse_matrix<float, float> m2(3);
    test_swap_columns(m2, 0, 1);
    m2(0, 0) = 3;
    test_swap_columns(m2, 0, 1);
    m2(0, 2) = 3;
    test_swap_columns(m2, 0, 2);
}



void test_swap_operations() {
    test_swap_rows();
    test_swap_columns();
}

void test_dense_matrix() {
    dense_matrix<double, double> d(3, 2);
    d.set_elem(0, 0, 1);
    d.set_elem(1, 1, 2);
    d.set_elem(2, 0, 3);
    // print_matrix(d);

    dense_matrix<double, double> unit(2, 2);
    d.set_elem(0, 0, 1);
    d.set_elem(1, 1, 1);

    dense_matrix<double, double> c = d * unit;

    // print_matrix(d);

    dense_matrix<double, double> perm(3, 3);
    perm.set_elem(0, 1, 1);
    perm.set_elem(1, 0, 1);
    perm.set_elem(2, 2, 1);
    auto c1 = perm * d;
    // print_matrix(c1);


    dense_matrix<double, double> p2(2, 2);
    p2.set_elem(0, 1, 1);
    p2.set_elem(1, 0, 1);
    auto c2 = d * p2;
}
#endif



std::vector<permutation_matrix<double, double>> vector_of_permutaions() {
    std::vector<permutation_matrix<double, double>> ret;
    {
        permutation_matrix<double, double> p0(5);
        p0[0] = 1; p0[1] = 2; p0[2] = 3; p0[3] = 4;
        p0[4] = 0;
        ret.push_back(p0);
    }
    {
        permutation_matrix<double, double> p0(5);
        p0[0] = 2; p0[1] = 0; p0[2] = 1; p0[3] = 4;
        p0[4] = 3;
        ret.push_back(p0);
    }
    return ret;
}

void test_apply_reverse_from_right_to_perm(permutation_matrix<double, double> & l) {
    permutation_matrix<double, double> p(5);
    p[0] = 4; p[1] = 2; p[2] = 0; p[3] = 3;
    p[4] = 1;

    permutation_matrix<double, double> pclone(5);
    pclone[0] = 4; pclone[1] = 2; pclone[2] = 0; pclone[3] = 3;
    pclone[4] = 1;

    p.multiply_by_reverse_from_right(l);
#ifdef LEAN_DEBUG
    auto rev = l.get_inverse();
    auto rs = pclone * rev;
    lean_assert(p == rs)
#endif
}

void test_apply_reverse_from_right() {
    auto vec = vector_of_permutaions();
    for (unsigned i = 0; i < vec.size(); i++) {
        test_apply_reverse_from_right_to_perm(vec[i]);
    }
}

void test_permutations() {
    test_apply_reverse_from_right();
}

#ifdef LEAN_DEBUG
void test_perm_apply_reverse_from_right() {
    permutation_generator<double, double> allp(5);
    vector<double> w(6);
    for (int i = 0; i < 5; i ++) {
        w[i] = i;
    }

    while (allp.move_next()){
        allp.current()->apply_reverse_from_right(w);
    }
}
#endif
void lp_solver_test() {
    // lp_revised_solver<double> lp_revised;
    // lp_revised.get_minimal_solution();
}

bool get_int_from_args_parser(const char * option, argument_parser & args_parser, unsigned & n) {
    string s = args_parser.get_option_value(option);
    if (s.size() > 0) {
        n = atoi(s.c_str());
        return true;
    }
    return false;
}

bool get_double_from_args_parser(const char * option, argument_parser & args_parser, double & n) {
    string s = args_parser.get_option_value(option);
    if (s.size() > 0) {
        n = atof(s.c_str());
        return true;
    }
    return false;
}


void update_settings(argument_parser & args_parser, lp_settings& settings) {
    unsigned n;
    if (get_int_from_args_parser("--rep_frq", args_parser, n))
        settings.report_frequency = n;
    else
        settings.report_frequency = 1000;

    if (get_int_from_args_parser("--percent_for_enter", args_parser, n))
        settings.percent_of_entering_to_check = n;
    if (get_int_from_args_parser("--partial_pivot", args_parser, n)) {
        cout << "setting partial pivot constant to " << n << std::endl;
        settings.c_partial_pivoting = n;
    }
    if (get_int_from_args_parser("--density", args_parser, n)) {
        double density = static_cast<double>(n) / 100.0;
        cout << "setting density to " << density << std::endl;
        settings.density_threshold = density;
    }
    if (get_int_from_args_parser("--maxng", args_parser, n))
        settings.max_number_of_iterations_with_no_improvements = n;
    double d;
    if (get_double_from_args_parser("--harris_toler", args_parser, d)) {
        cout << "setting harris_feasibility_tolerance to " << d << std::endl;
        settings.harris_feasibility_tolerance = d;
    }
}


void setup_solver(unsigned max_iterations, unsigned time_limit, bool look_for_min, argument_parser & args_parser, lp_solver<double, double> * solver) {
    if (max_iterations > 0)
        solver->set_max_iterations_per_stage(max_iterations);

    if (time_limit > 0)
        solver->set_time_limit(time_limit);

    if (look_for_min)
        solver->flip_costs();

    update_settings(args_parser, solver->settings());
}

bool values_are_one_percent_close(double a, double b);

void print_x(mps_reader<double, double> & reader, lp_solver<double, double> * solver) {
    for (auto name : reader.column_names()) {
        std::cout << name << "=" << solver->get_column_value_by_name(name) << ' ';
    }
    cout << std::endl;
}

void compare_solutions(mps_reader<double, double> & reader, lp_solver<double, double> * solver, lp_solver<double, double> * solver0) {
    for (auto name : reader.column_names()) {
        double a = solver->get_column_value_by_name(name);
        double b = solver0->get_column_value_by_name(name);
        if (!values_are_one_percent_close(a, b)) {
            cout << "different values for " << name << ":" << a << " and "  << b << std::endl;
        }
    }
}


void solve_mps_double(std::string file_name, bool look_for_min, unsigned max_iterations, unsigned time_limit, bool dual, bool compare_with_primal, argument_parser & args_parser) {
    mps_reader<double, double> reader(file_name);
    reader.read();
    if (!reader.is_ok()) {
        std::cout << "cannot process " << file_name << std::endl;
        return;
    }
    lp_solver<double, double> * solver =  reader.create_solver(dual);
    setup_solver(max_iterations, time_limit, look_for_min, args_parser, solver);
    int begin = get_millisecond_count();
    if (dual) {
        cout << "solving for dual" << std::endl;
    }
    solver->find_maximal_solution();
    int span = get_millisecond_span(begin);
    std::cout << "Status: " << lp_status_to_string(solver->get_status()) << std::endl;
    if (solver->get_status() == lp_status::OPTIMAL) {
        if (reader.column_names().size() < 20) {
            print_x(reader, solver);
        }
        double cost = solver->get_current_cost();
        if (look_for_min) {
            cost = -cost;
        }
        std::cout << "cost = " << cost << std::endl;
    }
    cout << "processed in " << span / 1000.0  << " seconds, running for " << solver->m_total_iterations << " iterations" << std::endl;
    if (compare_with_primal) {
        auto * primal_solver = reader.create_solver(false);
        setup_solver(max_iterations, time_limit, look_for_min, args_parser, primal_solver);
        primal_solver->find_maximal_solution();
        if (solver->get_status() != primal_solver->get_status()) {
            cout << "statuses are different: dual " << lp_status_to_string(solver->get_status()) << " primal = " << lp_status_to_string(primal_solver->get_status()) << std::endl;
        } else {
            if (solver->get_status() == lp_status::OPTIMAL) {
                double cost = solver->get_current_cost();
                if (look_for_min) {
                    cost = -cost;
                }
                double primal_cost = primal_solver->get_current_cost();
                if (look_for_min) {
                    primal_cost = -primal_cost;
                }
                cout << "primal cost = " << primal_cost << std::endl;
                if (!values_are_one_percent_close(cost, primal_cost)) {
                    compare_solutions(reader, primal_solver, solver);
                    print_x(reader, primal_solver);
                    cout << "dual cost is " << cost << ", but primal cost is " << primal_cost << std::endl;
                    lean_assert(false);
                }
            }
        }
        delete primal_solver;
    }
    delete solver;
}

void solve_mps_rational(std::string file_name, bool look_for_min, unsigned max_iterations, unsigned time_limit, bool dual, argument_parser & /*args_parser*/) {
    mps_reader<mpq, mpq> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        if (look_for_min) {
            solver->flip_costs();
        }
        int begin = get_millisecond_count();
        if (max_iterations > 0) {
            solver->set_max_iterations_per_stage(max_iterations);
        }

        if (time_limit > 0) {
            solver->set_time_limit(time_limit);
        }
        solver->find_maximal_solution();
        std::cout << "Status: " << lp_status_to_string(solver->get_status()) << std::endl;

        if (solver->get_status() == lp_status::OPTIMAL) {
            // for (auto name: reader.column_names()) {
            //  std::cout << name << "=" << solver->get_column_value_by_name(name) << ' ';
            // }
            mpq cost = solver->get_current_cost();
            if (look_for_min) {
                cost = -cost;
            }
            std::cout << "cost = " << cost.get_double() << std::endl;
        }
        cout << "processed in " << get_millisecond_span(begin) / 1000.0 << " seconds, running for " << solver->m_total_iterations << " iterations" << std::endl;
        delete solver;
    } else {
        std::cout << "cannot process " << file_name << std::endl;
    }
}
void get_time_limit_and_max_iters_from_parser(argument_parser & args_parser, unsigned & time_limit, unsigned & max_iters); // forward definition

void solve_mps(std::string file_name, bool look_for_min, unsigned max_iterations, unsigned time_limit, bool solve_for_rational, bool dual, bool compare_with_primal, argument_parser & args_parser) {
    if (!solve_for_rational) {
        std::cout << "solving " << file_name << std::endl;
        solve_mps_double(file_name, look_for_min, max_iterations, time_limit, dual, compare_with_primal, args_parser);
    } else {
        std::cout << "solving " << file_name << " in rationals " << std::endl;
        solve_mps_rational(file_name, look_for_min, max_iterations, time_limit, dual, args_parser);
    }
}

void solve_mps(string file_name, argument_parser & args_parser) {
    bool look_for_min = args_parser.option_is_used("--min");
    unsigned max_iterations, time_limit;
    bool solve_for_rational = args_parser.option_is_used("--mpq");
    bool dual = args_parser.option_is_used("--dual");
    bool compare_with_primal = args_parser.option_is_used("--compare_with_primal");
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iterations);
    solve_mps(file_name, look_for_min, max_iterations, time_limit, solve_for_rational, dual, compare_with_primal, args_parser);
}

void solve_mps_in_rational(std::string file_name, bool dual, argument_parser & /*args_parser*/) {
    std::cout << "solving " << file_name << std::endl;

    mps_reader<mpq, mpq> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        solver->find_maximal_solution();
        std::cout << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
        if (solver->get_status() == lp_status::OPTIMAL) {
            if (reader.column_names().size() < 20) {
                for (auto name : reader.column_names()) {
                    std::cout << name << "=" << solver->get_column_value_by_name(name).get_double() << ' ';
                }
            }
            std::cout << std::endl << "cost = " << numeric_traits<mpq>::get_double(solver->get_current_cost()) << std::endl;
        }
        delete solver;
    } else {
        std::cout << "cannot process " << file_name << std::endl;
    }
}

void test_upair_queue() {
    int n = 10;
    binary_heap_upair_queue<int> q(2);
    unordered_map<upair, int> m;
    for (int k = 0; k < 100; k++) {
        int i = my_random()%n;
        int j = my_random()%n;
        q.enqueue(i, j, my_random()%n);
    }

    q.remove(5, 5);

    while (!q.is_empty()) {
        unsigned i, j;
        q.dequeue(i, j);
    }
}

void test_binary_priority_queue() {
    cout << "testing binary_heap_priority_queue...";
    auto q = binary_heap_priority_queue<int>(10);
    q.enqueue(2, 2);
    q.enqueue(1, 1);
    q.enqueue(9, 9);
    q.enqueue(8, 8);
    q.enqueue(5, 25);
    q.enqueue(3, 3);
    q.enqueue(4, 4);
    q.enqueue(7, 30);
    q.enqueue(6, 6);
    q.enqueue(0, 0);
    q.enqueue(5, 5);
    q.enqueue(7, 7);

    for (unsigned i = 0; i < 10; i++) {
        unsigned de = q.dequeue();
        lean_assert(i == de);
        cout << de << std::endl;
    }
    q.enqueue(2, 2);
    q.enqueue(1, 1);
    q.enqueue(9, 9);
    q.enqueue(8, 8);
    q.enqueue(5, 5);
    q.enqueue(3, 3);
    q.enqueue(4, 4);
    q.enqueue(7, 2);
    q.enqueue(0, 1);
    q.enqueue(6, 6);
    q.enqueue(7, 7);
    q.enqueue(33, 1000);
    q.enqueue(20, 0);
    q.dequeue();
    q.remove(33);
    q.enqueue(0, 0);
#ifdef LEAN_DEBUG
    unsigned t = 0;
#endif
    while (q.size() > 0) {
        unsigned d =q.dequeue();
        lean_assert(t++ == d);
        cout << d << std::endl;
    }

    test_upair_queue();
    cout << " done" << std::endl;
}

bool solution_is_feasible(std::string file_name, const std::unordered_map<string, double> & solution) {
    mps_reader<double, double> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        lp_primal_simplex<double, double> * solver = static_cast<lp_primal_simplex<double, double> *>(reader.create_solver(false));
        return solver->solution_is_feasible(solution);
    }
    return false;
}


void solve_mps_with_known_solution(std::string file_name, std::unordered_map<string, double> * solution, lp_status status, bool dual) {
    std::cout << "solving " << file_name << std::endl;
    mps_reader<double, double> reader(file_name);
    reader.read();
    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        solver->find_maximal_solution();
        std::cout << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
        if (status != solver->get_status()){
            cout << "status should be " << lp_status_to_string(status) << std::endl;
            lean_assert(status == solver->get_status());
            throw "status is wrong";
        }
        if (solver->get_status() == lp_status::OPTIMAL) {
            std::cout << "cost = " << solver->get_current_cost() << std::endl;
            if (solution != nullptr) {
                for (auto it : *solution) {
                    if (fabs(it.second - solver->get_column_value_by_name(it.first)) >= 0.000001) {
                        std::cout << "expected:" << it.first << "=" <<
                            it.second <<", got " << solver->get_column_value_by_name(it.first) << std::endl;
                    }
                    lean_assert(fabs(it.second - solver->get_column_value_by_name(it.first)) < 0.000001);
                }
            }
            if (reader.column_names().size() < 20) {
                for (auto name : reader.column_names()) {
                    std::cout << name << "=" << solver->get_column_value_by_name(name) << ' ';
                }
                cout << std::endl;
            }
        }
        delete solver;
    } else {
        std::cout << "cannot process " << file_name << std::endl;
    }
}

int get_random_rows() {
    return 5 + my_random() % 2;
}

int get_random_columns() {
    return 5 + my_random() % 3;
}

int get_random_int() {
    return -1 + my_random() % 2; // (1.0 + RAND_MAX);
}

void add_random_row(lp_primal_simplex<double, double> * solver, int cols, int row) {
    solver->add_constraint(lp_relation::Greater_or_equal, 1, row);
    for (int i = 0; i < cols; i++) {
        solver->set_row_column_coefficient(row, i, get_random_int());
    }
}

void add_random_cost(lp_primal_simplex<double, double> * solver, int cols) {
    for (int i = 0; i < cols; i++) {
        solver->set_cost_for_column(i, get_random_int());
    }
}

lp_primal_simplex<double, double> * generate_random_solver() {
    int rows = get_random_rows();
    int cols = get_random_columns();
    auto * solver = new lp_primal_simplex<double, double>();
    for (int i = 0; i < rows; i++) {
        add_random_row(solver, cols, i);
    }
    add_random_cost(solver, cols);
    return solver;
}



void random_test_on_i(unsigned i) {
    if (i % 1000 == 0) {
        cout << ".";
    }
    srand(i);
    auto *solver = generate_random_solver();
    solver->find_maximal_solution();
    //    cout << lp_status_to_string(solver->get_status()) << std::endl;
    delete solver;
}

void random_test() {
    for (unsigned i = 0; i < std::numeric_limits<unsigned>::max(); i++) {
        try {
            random_test_on_i(i);
        }
        catch (const char * error) {
            cout << "i = " << i << ", throwing at ' " << error << "'" << std::endl;
            break;
        }
    }
}


void fill_file_names(std::vector<std::string> &file_names,  std::set<string> & minimums) {
    char *home_dir = getenv("HOME");
    if (home_dir == nullptr) {
        cout << "cannot find home directory, don't know how to find the files";
        return;
    }
    string home_dir_str(home_dir);
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l0redund.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l1.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l2.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l3.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l4.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l4fix.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/plan.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/samp2.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/murtagh.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/l0.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AFIRO.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC50B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC50A.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/KB2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC105.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STOCFOR1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/ADLITTLE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BLEND.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCAGR7.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SC205.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHARE2B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/RECIPELP.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/LOTFI.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/VTP-BASE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHARE1B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BOEING2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BORE3D.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCORPION.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/CAPRI.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BRANDY.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCAGR25.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/ISRAEL.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCFXM1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BANDM.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/E226.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AGG.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GROW7.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/ETAMACRO.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FINNIS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCSD1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STANDATA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STANDGUB.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BEACONFD.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STAIR.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STANDMPS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GFRD-PNC.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCRS8.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BOEING1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/MODSZK1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/DEGEN2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FORPLAN.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AGG2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/AGG3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCFXM2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHELL.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT4.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCSD6.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP04S.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SEBA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GROW15.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FFFFF800.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BNL1.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PEROLD.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/QAP8.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCFXM3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP04L.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GANGES.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GROW22.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP08S.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT-WE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/MAROS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STOCFOR2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/25FV47.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP12S.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCSD8.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT1P.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SIERRA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOTNOV.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/CZPROB.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT1D.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT-JA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP08L.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/BNL2.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/NESM.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/CYCLE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/acc-tight5.mps");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/SHIP12L.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/DEGEN3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEA.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEB.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/80BAU3B.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/TRUSS.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/D2Q06C.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/WOODW.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/QAP12.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/D6CUBE.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/DFL001.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/WOOD1P.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT2P.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/PILOT87.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/STOCFOR3.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/QAP15.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/FIT2D.SIF");
    file_names.push_back(home_dir_str + "/projects/lean/src/tests/util/lp/test_files/netlib/MAROS-R7.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/FIT2P.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/DFL001.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/D2Q06C.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/80BAU3B.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEB.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/GREENBEA.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/BNL2.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SHIP08L.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/FIT1D.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SCTAP3.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SCSD8.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/SCSD6.SIF");
    minimums.insert("/projects/lean/src/tests/util/lp/test_files/netlib/MAROS-R7.SIF");
}

void test_out_dir(string out_dir) {
    DIR *out_dir_p = opendir(out_dir.c_str());
    if (out_dir_p == nullptr) {
        cout << "creating directory " << out_dir << std::endl;
#ifdef LEAN_WINDOWS
        int res = mkdir(out_dir.c_str());
#else
        int res = mkdir(out_dir.c_str(), S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
#endif
        if (res) {
            cout << "Cannot open output directory \"" << out_dir << "\"" << std::endl;
        }
        return;
    }
    closedir(out_dir_p);
}

void find_dir_and_file_name(string a, string & dir, string& fn) {
    // todo: make it system independent
    size_t last_slash_pos = a.find_last_of("/");
    if (last_slash_pos >= a.size()) {
        cout << "cannot find file name in " << a << std::endl;
        throw;
    }
    dir = a.substr(0, last_slash_pos);
    // cout << "dir = " << dir << std::endl;
    fn = a.substr(last_slash_pos + 1);
    //    cout << "fn = " << fn << std::endl;
}

void process_test_file(string test_dir, string test_file_name, argument_parser & args_parser, string out_dir, unsigned max_iters, unsigned time_limit, unsigned & successes, unsigned & failures, unsigned & inconclusives);

void solve_some_mps(argument_parser & args_parser) {
    unsigned max_iters, time_limit;
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iters);
    unsigned successes = 0;
    unsigned failures = 0;
    unsigned inconclusives = 0;
    std::set<string> minimums;
    std::vector<std::string> file_names;
    fill_file_names(file_names, minimums);
    bool solve_for_rational = args_parser.option_is_used("--mpq");
    bool dual = args_parser.option_is_used("--dual");
    bool compare_with_primal = args_parser.option_is_used("--compare_with_primal");
    bool compare_with_glpk = args_parser.option_is_used("--compare_with_glpk");
    if (compare_with_glpk) {
        string out_dir = args_parser.get_option_value("--out_dir");
        if (out_dir.size() == 0) {
            out_dir = "/tmp/test";
        }
        test_out_dir(out_dir);
        for (auto& a : file_names) {
            try {
                string file_dir;
                string file_name;
                find_dir_and_file_name(a, file_dir, file_name);
                process_test_file(file_dir, file_name, args_parser, out_dir, max_iters, time_limit, successes, failures, inconclusives);
            }
            catch(const char *s){
                std::cout<< "exception: "<< s << std::endl;
            }
        }
        cout << "comparing with glpk: successes " << successes << ", failures " << failures << ", inconclusives " << inconclusives << std::endl;
        return;
    }
    if (!solve_for_rational) {
        solve_mps(file_names[6], false, 0, time_limit, false, dual, compare_with_primal, args_parser);
        solve_mps_with_known_solution(file_names[3], nullptr, INFEASIBLE, dual); // chvatal: 135(d)
        std::unordered_map<std::string, double> sol;
        sol["X1"] = 0;
        sol["X2"] = 6;
        sol["X3"] = 0;
        sol["X4"] = 15;
        sol["X5"] = 2;
        sol["X6"] = 1;
        sol["X7"] = 1;
        sol["X8"] = 0;
        solve_mps_with_known_solution(file_names[9], &sol, OPTIMAL, dual);
        solve_mps_with_known_solution(file_names[0], &sol, OPTIMAL, dual);
        sol.clear();
        sol["X1"] = 25.0/14.0;
        // sol["X2"] = 0;
        // sol["X3"] = 0;
        // sol["X4"] = 0;
        // sol["X5"] = 0;
        // sol["X6"] = 0;
        // sol["X7"] = 9.0/14.0;
        solve_mps_with_known_solution(file_names[5], &sol, OPTIMAL, dual); // chvatal: 135(e)
        solve_mps_with_known_solution(file_names[4], &sol, OPTIMAL, dual); // chvatal: 135(e)
        solve_mps_with_known_solution(file_names[2], nullptr, UNBOUNDED, dual); // chvatal: 135(c)
        solve_mps_with_known_solution(file_names[1], nullptr, UNBOUNDED, dual); // chvatal: 135(b)
        solve_mps(file_names[8], false, 0, time_limit, false, dual, compare_with_primal, args_parser);
        // return;
        for (auto& s : file_names) {
            try {
                solve_mps(s, minimums.find(s) != minimums.end(), max_iters, time_limit, false, dual, compare_with_primal, args_parser);
            }
            catch(const char *s){
                std::cout<< "exception: "<< s << std::endl;
            }
        }
    } else {
        unsigned i = 0;
        for (auto& s : file_names) {
            if (i++ > 9) return;
            try {
                solve_mps_in_rational(s, dual, args_parser);
            }
            catch(const char *s){
                std::cout<< "exception: "<< s << std::endl;
            }
        }
    }
}

void solve_rational() {
    lp_primal_simplex<mpq, mpq> solver;
    solver.add_constraint(lp_relation::Equal, mpq(7), 0);
    solver.add_constraint(lp_relation::Equal, mpq(-3), 1);

    // setting the cost
    int cost[] = {-3, -1, -1, 2, -1, 1, 1, -4};
    std::string var_names[8] = {"x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8"};

    for (unsigned i = 0; i < 8; i++) {
        solver.set_cost_for_column(i, mpq(cost[i]));
        solver.give_symbolic_name_to_column(var_names[i], i);
    }

    int row0[] = {1, 0, 3, 1, -5, -2 , 4, -6};
    for (unsigned i = 0; i < 8; i++) {
        solver.set_row_column_coefficient(0, i, mpq(row0[i]));
    }

    int row1[] = {0, 1, -2, -1, 4, 1, -3, 5};
    for (unsigned i = 0; i < 8; i++) {
        solver.set_row_column_coefficient(1, i, mpq(row1[i]));
    }

    int bounds[] = {8, 6, 4, 15, 2, 10, 10, 3};
    for (unsigned i = 0; i < 8; i++) {
        solver.set_low_bound(i, mpq(0));
        solver.set_upper_bound(i, mpq(bounds[i]));
    }

    std::unordered_map<std::string, mpq>  expected_sol;
    expected_sol["x1"] = mpq(0);
    expected_sol["x2"] = mpq(6);
    expected_sol["x3"] = mpq(0);
    expected_sol["x4"] = mpq(15);
    expected_sol["x5"] = mpq(2);
    expected_sol["x6"] = mpq(1);
    expected_sol["x7"] = mpq(1);
    expected_sol["x8"] = mpq(0);
    solver.find_maximal_solution();
    lean_assert(solver.get_status() == OPTIMAL);
    for (auto it : expected_sol) {
        lean_assert(it.second == solver.get_column_value_by_name(it.first));
    }
}


string read_line(bool & end, ifstream & file) {
    string s;
    if (!getline(file, s)) {
        end = true;
        return string();
    }
    end = false;
    return s;
}

bool contains(string const & s, char const * pattern) {
    return s.find(pattern) != string::npos;
}


unordered_map<string, double> * get_solution_from_glpsol_output(string & file_name) {
    ifstream file(file_name);
    if (!file.is_open()){
        cerr << "cannot  open " << file_name << std::endl;
        return nullptr;
    }
    string s;
    bool end;
    do {
        s = read_line(end, file);
        if (end) {
            cerr << "unexpected file end " << file_name << std::endl;
            return nullptr;
        }
        if (contains(s, "Column name")){
            break;
        }
    } while (true);

    read_line(end, file);
    if (end) {
        cerr << "unexpected file end " << file_name << std::endl;
        return nullptr;
    }

    auto ret = new unordered_map<string, double>();

    do {
        s = read_line(end, file);
        if (end) {
            cerr << "unexpected file end " << file_name << std::endl;
            return nullptr;
        }
        auto split = string_split(s, " \t", false);
        if (split.size() == 0) {
           return ret;
        }

        lean_assert(split.size() > 3);
        (*ret)[split[1]] = atof(split[3].c_str());
    } while (true);
}



void test_init_U() {
    static_matrix<double, double> m(3, 7);
    m(0, 0) = 10; m(0, 1) = 11; m(0, 2) = 12; m(0, 3) = 13; m(0, 4) = 14;
    m(1, 0) = 20; m(1, 1) = 21; m(1, 2) = 22; m(1, 3) = 23; m(1, 5) = 24;
    m(2, 0) = 30; m(2, 1) = 31; m(2, 2) = 32; m(2, 3) = 33; m(2, 6) = 34;
#ifdef LEAN_DEBUG
    print_matrix(m, std::cout);
#endif
    std::vector<unsigned> basis(3);
    basis[0] = 1;
    basis[1] = 2;
    basis[2] = 4;

    sparse_matrix<double, double> u(m, basis);

    for (unsigned i = 0; i < 3; i++) {
        for (unsigned j = 0; j < 3; j ++) {
            lean_assert(m(i, basis[j]) == u(i, j));
        }
    }

    // print_matrix(m);
    // print_matrix(u);
}

void test_replace_column() {
    sparse_matrix<float, float> m(10);
    fill_matrix(m);
    m.swap_columns(0, 7);
    m.swap_columns(6, 3);
    m.swap_rows(2, 0);
    for (unsigned i = 1; i < m.dimension(); i++) {
        m(i, 0) = 0;
    }

    indexed_vector<float> w(m.dimension());
    for (unsigned i = 0; i < m.dimension(); i++) {
        w.set_value(i % 3, i);
    }

    lp_settings settings;

    for (unsigned column_to_replace = 0;  column_to_replace < m.dimension(); column_to_replace ++) {
        m.replace_column(column_to_replace, w, settings);
        for (unsigned i = 0; i < m.dimension(); i++) {
            lean_assert(abs(w[i] - m(i, column_to_replace)) < 0.00000001);
        }
    }
}


void setup_args_parser(argument_parser & parser) {
    parser.add_option_with_after_string_with_help("--density", "the percentage of non-zeroes in the matrix below which it is not dense");
    parser.add_option_with_after_string_with_help("--harris_toler", "harris tolerance");
    parser.add_option_with_help_string("--test_swaps", "test row swaps with a permutation");
    parser.add_option_with_after_string_with_help("--checklu", "the file name for lu checking");
    parser.add_option_with_after_string_with_help("--partial_pivot", "the partial pivot constant, a number somewhere between 10 and 100");
    parser.add_option_with_after_string_with_help("--percent_for_enter", "which percent of columns check for entering column");
    parser.add_option_with_help_string("--totalinf", "minimizes the total infeasibility  instead of diminishin infeasibility of the rows");
    parser.add_option_with_after_string_with_help("--rep_frq", "the report frequency, in how many iterations print the cost and other info ");
    parser.add_option_with_help_string("--smt", "smt file format");
    parser.add_option_with_after_string_with_help("--filelist", "the file containing the list of files");
    parser.add_option_with_after_string_with_help("--file", "the input file name");
    parser.add_option_with_help_string("--min", "will look for the minimum for the given file if --file is used; the default is looking for the max");
    parser.add_option_with_help_string("--max", "will look for the maximum for the given file if --file is used; it is the default behavior");
    parser.add_option_with_after_string_with_help("--max_iters", "maximum total iterations in a core solver stage");
    parser.add_option_with_after_string_with_help("--time_limit", "time limit in seconds");
    parser.add_option_with_help_string("--mpq", "solve for rational numbers");
    parser.add_option_with_help_string("--test_lu", "test the work of the factorization");
    parser.add_option_with_help_string("--test_larger_lu", "test the work of the factorization");
    parser.add_option_with_help_string("--test_larger_lu_with_holes", "test the work of the factorization");
    parser.add_option_with_help_string("--test_lp_0", "solve a small lp");
    parser.add_option_with_help_string("--solve_some_mps", "solves a list of mps problems");
    parser.add_option_with_after_string_with_help("--test_file_directory", "loads files from the directory for testing");
    parser.add_option_with_help_string("--compare_with_glpk", "compares the results by running glpsol");
    parser.add_option_with_after_string_with_help("--out_dir", "setting the output directory for tests, if not set /tmp is used");
    parser.add_option_with_help_string("--dual", "using the dual simplex solver");
    parser.add_option_with_help_string("--compare_with_primal", "using the primal simplex solver for comparison");
    parser.add_option_with_help_string("--lar", "test lar_solver");
    parser.add_option_with_after_string_with_help("--maxng", "max iterations without progress");
    parser.add_option_with_help_string("-tbq", "test binary queue");
}

void solve_test_flipped(bool dual) {
    // solving a problem with a constraint xj <= c, a flipped constraint
    char * home_dir = getenv("HOME");
    if (home_dir == nullptr) {
        cout << "cannot find home directory" << std::endl;
        return;
    }
    string file_name = string(home_dir) + "/projects/lean/src/tests/util/lp/l4.mps";
    mps_reader<double, double> reader(file_name);
    reader.read();

    if (reader.is_ok()) {
        auto * solver =  reader.create_solver(dual);
        solver->find_maximal_solution();
        lean_assert(solver->get_status() == OPTIMAL);
        double x1_val = solver->get_column_value_by_name("X1");
        cout << "X1 = " << x1_val << std::endl;
        mps_reader<double, double> reader_(file_name);
        reader_.read();
        auto solver_ = reader_.create_solver(dual);
        int j = solver_ -> get_column_index_by_name("X1");
        lean_assert(j != -1)
        solver_-> unset_low_bound(j);
        solver_->set_upper_bound(j, x1_val + 1);
        solver_->find_maximal_solution();
        cout << "new X1 = " << solver_->get_column_value_by_name("X1") << std::endl;
        lean_assert(fabs(x1_val - solver_->get_column_value_by_name("X1")) < 1e-10);
        delete solver;
        delete solver_;
    }
}

template <typename T>
void print_chunk(T * arr, unsigned len) {
    for (unsigned i = 0; i < len; i++) {
        cout << arr[i] << ", ";
    }
    cout << std::endl;
}

struct mem_cpy_place_holder {
    static void mem_copy_hook(int * destination, unsigned num) {
        if (destination == nullptr || num == 0) {
            throw "bad parameters";
        }
    }
};

int finalize(unsigned ret) {
    finalize_util_module();
    finalize_numerics_module();
    return ret;
}

void get_time_limit_and_max_iters_from_parser(argument_parser & args_parser, unsigned & time_limit, unsigned & max_iters) {
    string s = args_parser.get_option_value("--max_iters");
    if (s.size() > 0) {
        max_iters = atoi(s.c_str());
    } else {
        max_iters = 0;
    }

    string time_limit_string = args_parser.get_option_value("--time_limit");
    if (time_limit_string.size() > 0) {
        time_limit = atoi(time_limit_string.c_str());
    } else {
        time_limit = 0;
    }
}


string create_output_file_name(bool minimize, string file_name, bool mpq) {
    string ret = file_name + "_lp_tst_" +  (minimize?"min":"max");
    if (mpq) return ret + "_mpq.out";
    return ret + ".out";
}

string create_output_file_name_for_glpsol(bool minimize, string file_name){
    return file_name + (minimize?"_min":"_max") + "_glpk_out";
}

int run_glpk(string file_name, string glpk_out_file_name, bool minimize, unsigned time_limit) {
    string minmax(minimize?"--min":"--max");
    string tmlim = time_limit > 0 ? string(" --tmlim ")  + std::to_string(time_limit)+ " ":string();
    string command_line =  string("glpsol --nointopt --nomip ") +  minmax + tmlim +  + " -o " + glpk_out_file_name +" " + file_name + " > /dev/null";
    return system(command_line.c_str());
}

string get_status(string file_name) {
    std::ifstream f(file_name);
    if (!f.is_open()) {
        cout << "cannot open " << file_name << std::endl;
        throw 0;
    }
    string str;
    while (getline(f, str)) {
        if (str.find("Status") != string::npos) {
            vector<string> tokens = split_and_trim(str);
            if (tokens.size() != 2) {
                cout << "unexpected Status string " << str << std::endl;
                throw 0;
            }
            return tokens[1];
        }
    }
    cout << "cannot find the status line in " << file_name << std::endl;
    throw 0;
}

// returns true if the costs should be compared too
bool compare_statuses(string glpk_out_file_name, string lp_out_file_name, unsigned & successes, unsigned & failures) {
    string glpk_status = get_status(glpk_out_file_name);
    string lp_tst_status = get_status(lp_out_file_name);

    if (glpk_status != lp_tst_status) {
        if (glpk_status == "UNDEFINED"  && (lp_tst_status == "UNBOUNDED" || lp_tst_status == "INFEASIBLE")) {
            successes++;
            return false;
        } else {
            cout << "glpsol and lp_tst disagree: glpsol status is " << glpk_status;
            cout << " but lp_tst status is " << lp_tst_status << std::endl;
            failures++;
            return false;
        }
    }
    return lp_tst_status == "OPTIMAL";
}

double get_glpk_cost(string file_name) {
    std::ifstream f(file_name);
    if (!f.is_open()) {
        cout << "cannot open " << file_name << std::endl;
        throw 0;
    }
    string str;
    while (getline(f, str)) {
        if (str.find("Objective") != string::npos) {
            vector<string> tokens = split_and_trim(str);
            if (tokens.size() != 5) {
                cout << "unexpected Objective string " << str << std::endl;
                throw 0;
            }
            return atof(tokens[3].c_str());
        }
    }
    cout << "cannot find the Objective line in " << file_name << std::endl;
    throw 0;
}

double get_lp_tst_cost(string file_name) {
    std::ifstream f(file_name);
    if (!f.is_open()) {
        cout << "cannot open " << file_name << std::endl;
        throw 0;
    }
    string str;
    string cost_string;
    while (getline(f, str)) {
        if (str.find("cost") != string::npos) {
            cost_string = str;
        }
    }
    if (cost_string.size() == 0) {
        cout << "cannot find the cost line in " << file_name << std::endl;
        throw 0;
    }

    vector<string> tokens = split_and_trim(cost_string);
    if (tokens.size() != 3) {
        cout << "unexpected cost string " << cost_string << std::endl;
        throw 0;
    }
    return atof(tokens[2].c_str());
}

bool values_are_one_percent_close(double a, double b) {
    double maxval = std::max(fabs(a), fabs(b));
    if (maxval < 0.000001) {
        return true;
    }

    double one_percent = maxval / 100;
    return fabs(a - b) <= one_percent;
}

// returns true if both are optimal
void compare_costs(string glpk_out_file_name,
                    string lp_out_file_name,
                   unsigned & successes,
                   unsigned & failures) {
    double a = get_glpk_cost(glpk_out_file_name);
    double b = get_lp_tst_cost(lp_out_file_name);

    if (values_are_one_percent_close(a, b)) {
        successes++;
    } else {
        failures++;
        cout << "glpsol cost is " << a << " lp_tst cost is " << b << std::endl;
    }
}



void compare_with_glpk(string glpk_out_file_name, string lp_out_file_name, unsigned & successes, unsigned & failures, string /*lp_file_name*/) {
#ifdef CHECK_GLPK_SOLUTION
    std::unordered_map<string, double> * solution_table =  get_solution_from_glpsol_output(glpk_out_file_name);
    if (solution_is_feasible(lp_file_name, *solution_table)) {
        cout << "glpk solution is feasible" << std::endl;
    } else {
        cout << "glpk solution is infeasible" << std::endl;
    }
    delete solution_table;
#endif
    if (compare_statuses(glpk_out_file_name, lp_out_file_name, successes, failures)) {
        compare_costs(glpk_out_file_name, lp_out_file_name, successes, failures);
    }
}
void test_lar_on_file(string file_name, argument_parser & args_parser);

void process_test_file(string test_dir, string test_file_name, argument_parser & args_parser, string out_dir, unsigned max_iters, unsigned time_limit, unsigned & successes, unsigned & failures, unsigned & inconclusives) {
    bool use_mpq = args_parser.option_is_used("--mpq");
    bool minimize = args_parser.option_is_used("--min");
    string full_lp_tst_out_name = out_dir + "/" + create_output_file_name(minimize, test_file_name, use_mpq);

    string input_file_name = test_dir + "/" + test_file_name;
    if (input_file_name[input_file_name.size() - 1] == '~') {
        //        cout << "ignoring " << input_file_name << std::endl;
        return;
    }
    cout <<"processing " <<  input_file_name << std::endl;

    std::ofstream out(full_lp_tst_out_name);
    if (!out.is_open()) {
        cout << "cannot open file " << full_lp_tst_out_name << std::endl;
        throw 0;
    }
    std::streambuf *coutbuf = std::cout.rdbuf(); // save old buffer
    std::cout.rdbuf(out.rdbuf()); // redirect std::cout to dir_entry->d_name!
    bool dual = args_parser.option_is_used("--dual");
    try {
        if (args_parser.option_is_used("--lar"))
            test_lar_on_file(input_file_name, args_parser);
        else
            solve_mps(input_file_name, minimize, max_iters, time_limit, use_mpq, dual, false, args_parser);
    }
    catch(...) {
        cout << "catching the failure" << std::endl;
        failures++;
        std::cout.rdbuf(coutbuf); // reset to standard output again
        return;
    }
    std::cout.rdbuf(coutbuf); // reset to standard output again

    if (args_parser.option_is_used("--compare_with_glpk")) {
        string glpk_out_file_name =  out_dir + "/" + create_output_file_name_for_glpsol(minimize, string(test_file_name));
        int glpk_exit_code = run_glpk(input_file_name, glpk_out_file_name, minimize, time_limit);
        if (glpk_exit_code != 0) {
            cout << "glpk failed" << std::endl;
            inconclusives++;
        } else {
            compare_with_glpk(glpk_out_file_name, full_lp_tst_out_name, successes, failures, input_file_name);
        }
    }
}
int my_readdir(DIR *dirp, struct dirent *
#ifndef LEAN_WINDOWS
               entry
#endif
               , struct dirent **result) {
#ifdef LEAN_WINDOWS
    *result = readdir(dirp); // NOLINT
    return *result != nullptr? 0 : 1;
#else
    return readdir_r(dirp, entry, result);
#endif
}

std::vector<std::pair<std::string, int>> get_file_list_of_dir(std::string test_file_dir) {
    DIR *dir;
    if ((dir  = opendir(test_file_dir.c_str())) == nullptr) {
        std::cout << "Cannot open directory " << test_file_dir << std::endl;
        throw 0;
    }
    std::vector<std::pair<std::string, int>> ret;
    struct dirent entry;
    struct dirent* result;
    int return_code;
    for (return_code = my_readdir(dir, &entry, &result);
#ifndef LEAN_WINDOWS
         result != nullptr &&
#endif
         return_code == 0;
         return_code = my_readdir(dir, &entry, &result)) {
      DIR *tmp_dp = opendir(result->d_name);
        struct stat file_record;
        if (tmp_dp == nullptr) {
            std::string s = test_file_dir+ "/" + result->d_name;
            int stat_ret = stat(s.c_str(), & file_record);
            if (stat_ret!= -1) {
                ret.push_back(make_pair(result->d_name, file_record.st_size));
            } else {
                perror("stat");
                exit(1);
            }
        } else  {
            closedir(tmp_dp);
        }
    }
    closedir(dir);
    return ret;
}


struct file_size_comp {
    unordered_map<std::string, int>& m_file_sizes;
    file_size_comp(unordered_map<std::string, int>& fs) :m_file_sizes(fs) {}
    int operator()(std::string a, std::string b) {
        std::cout << m_file_sizes.size() << std::endl;
        std::cout << a << std::endl;
        std::cout << b << std::endl;

        auto ls = m_file_sizes.find(a);
        std::cout << "fa" << std::endl;
        auto rs = m_file_sizes.find(b);
        std::cout << "fb" << std::endl;
        if (ls != m_file_sizes.end() && rs != m_file_sizes.end()) {
            std::cout << "fc " << std::endl;
            int r = (*ls < *rs? -1: (*ls > *rs)? 1 : 0);
            std::cout << "calc r " << std::endl;
            return r;
        } else {
            std::cout << "sc " << std::endl;
            return 0;
        }
    }
};


struct sort_pred {
    bool operator()(const std::pair<std::string, int> &left, const std::pair<std::string, int> &right) {
        return left.second < right.second;
    }
};


void test_files_from_directory(std::string test_file_dir, argument_parser & args_parser) {
    std::cout << "loading files from directory \"" << test_file_dir << "\"" << std::endl;
    std::string out_dir = args_parser.get_option_value("--out_dir");
    if (out_dir.size() == 0) {
        out_dir = "/tmp/test";
    }
    DIR *out_dir_p = opendir(out_dir.c_str());
    if (out_dir_p == nullptr) {
        std::cout << "Cannot open output directory \"" << out_dir << "\"" << std::endl;
        return;
    }
    closedir(out_dir_p);
    std::vector<std::pair<std::string, int>> files = get_file_list_of_dir(test_file_dir);
    std::sort(files.begin(), files.end(), sort_pred());
    unsigned max_iters, time_limit;
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iters);
    unsigned successes = 0, failures = 0, inconclusives = 0;
    for  (auto & t : files) {
        process_test_file(test_file_dir, t.first, args_parser, out_dir, max_iters, time_limit, successes, failures, inconclusives);
    }
    std::cout << "comparing with glpk: successes " << successes << ", failures " << failures << ", inconclusives " << inconclusives << std::endl;
}


unordered_map<std::string, mpq> get_solution_map(lp_solver<mpq, mpq> * lps, mps_reader<mpq, mpq> & reader) {
    unordered_map<std::string, mpq> ret;
    for (auto it : reader.column_names()) {
        ret[it] = lps->get_column_value_by_name(it);
    }
    return ret;
}

void run_lar_solver(argument_parser & args_parser, lar_solver * solver, mps_reader<mpq, mpq> * reader) {
    std::string maxng = args_parser.get_option_value("--maxng");
    if (maxng.size() > 0) {
        solver->settings().max_number_of_iterations_with_no_improvements = atoi(maxng.c_str());
    }
    if (args_parser.option_is_used("--totalinf")) {
        solver->settings().row_feasibility = false;
    }
    if (args_parser.option_is_used("--mpq")) {
        solver->settings().use_double_solver_for_lar = false;
    }
    std::string iter = args_parser.get_option_value("--max_iters");
    if (iter.size() > 0) {
        solver->settings().max_total_number_of_iterations = atoi(iter.c_str());
    }
    if (args_parser.option_is_used("--compare_with_primal")){
        if (reader == nullptr) {
            std::cout << "cannot compare with primal, the reader is null " << std::endl;
            return;
        }
        auto * lps = reader->create_solver(false);
        lps->find_maximal_solution();
        unordered_map<std::string, mpq> sol = get_solution_map(lps, *reader);
        mpq inf = solver->get_infeasibility_of_solution(sol);
        std::cout << "inf with primal = " << inf <<  std::endl;
        return;
    }
    int begin = get_millisecond_count();
    lp_status status = solver->check();
    std::cout << "status is " <<  lp_status_to_string(status) << ", processed for " << get_millisecond_span(begin) / 1000.0 <<" seconds, and " << solver->get_total_iterations() << " iterations" << std::endl;
    if (solver->get_status() == INFEASIBLE) {
        buffer<std::pair<mpq, constraint_index>> evidence;
        solver->get_infeasibility_evidence(evidence);
    }
}

void test_lar_on_file(std::string file_name, argument_parser & args_parser) {
    lar_solver * solver = nullptr;
    std::cout << "processing " << file_name << std::endl;
    if (args_parser.option_is_used("--smt")) {
        smt_reader reader(file_name);
        reader.read();
        if (!reader.is_ok()){
            std::cout << "cannot process " << file_name << std::endl;
            return;
        }
        solver = reader.create_lar_solver();
        run_lar_solver(args_parser, solver, nullptr);
        delete solver;
        return;
    }
    mps_reader<mpq, mpq> reader(file_name);
    reader.read();
    if (!reader.is_ok()) {
        std::cout << "cannot process " << file_name << std::endl;
        return;
    }
    solver =  reader.create_lar_solver();
    run_lar_solver(args_parser, solver, & reader);
    delete solver;
}

vector<std::string> get_file_names_from_file_list(std::string filelist) {
    ifstream file(filelist);
    if (!file.is_open()) {
        std::cout << "cannot open " << filelist << std::endl;
        return vector<std::string>();
    }
    vector<std::string> ret;
    bool end;
    do {
        std::string s = read_line(end, file);
        if (end)
            break;
        if (s.size() == 0)
            break;
        ret.push_back(s);
    } while (true);
    return ret;
}

void test_lar_solver(argument_parser & args_parser) {
    std::string file_name = args_parser.get_option_value("--file");
    if (file_name.size() > 0) {
        test_lar_on_file(file_name, args_parser);
        return;
    }

    std::string file_list = args_parser.get_option_value("--filelist");
    if (file_list.size() > 0) {
        for (std::string fn : get_file_names_from_file_list(file_list))
            test_lar_on_file(fn, args_parser);
        return;
    }
}

void test_numeric_pair() {
    numeric_pair<mpq> a;
    numeric_pair<mpq> b(2, mpq(6, 2));
    a = b;
    numeric_pair<mpq> c(0.1, 0.5);
    a += 2*c;
    a -= c;
    lean_assert (a == b + c);
    numeric_pair<mpq> d = a * 2;
    std::cout << a  << std::endl;
    lean_assert(b == b);
    lean_assert(b < a);
    lean_assert(b <= a);
    lean_assert(a > b);
    lean_assert(a != b);
    lean_assert(a >= b);
    lean_assert(-a < b);
    lean_assert(a < 2 * b);
    lean_assert(b + b > a);
    lean_assert(mpq(2.1) * b + b > a);
    lean_assert(-b * mpq(2.1) - b < mpq(0.99)  * a);
    std::cout << - b * mpq(2.1) - b << std::endl;
    lean_assert(-b *(mpq(2.1) + 1) == - b * mpq(2.1) - b);
}

void get_matrix_dimensions(ifstream & f, unsigned & m, unsigned & n) {
    std::string line;
    getline(f, line);
    getline(f, line);
    vector<std::string> r = split_and_trim(line);
    m = atoi(r[1].c_str());
    getline(f, line);
    r = split_and_trim(line);
    n = atoi(r[1].c_str());
}

void read_row_cols(unsigned i, static_matrix<double, double>& A, ifstream & f) {
    do {
        std::string line;
        getline(f, line);
        if (line== "row_end")
            break;
        auto r = split_and_trim(line);
        lean_assert(r.size() == 4);
        unsigned j = atoi(r[1].c_str());
        double v = atof(r[3].c_str());
        A.set(i, j, v);
    } while (true);
}

bool read_row(static_matrix<double, double> & A, ifstream & f) {
    std::string line;
    getline(f, line);
    if (static_cast<int>(line.find("row")) == -1)
        return false;
    auto r = split_and_trim(line);
    if (r[0] != "row")
        std::cout << "wrong row line" << line << std::endl;
    unsigned i = atoi(r[1].c_str());
    read_row_cols(i, A, f);
    return true;
}

void read_rows(static_matrix<double, double>& A, ifstream & f) {
    while (read_row(A, f)) {}
}

void read_basis(vector<unsigned> & basis, ifstream & f) {
    std::cout << "reading basis" << std::endl;
    std::string line;
    getline(f, line);
    lean_assert(line == "basis_start");
    do {
        getline(f, line);
        if (line == "basis_end")
            break;
        unsigned j = atoi(line.c_str());
        basis.push_back(j);
    } while (true);
}

void read_indexed_vector(indexed_vector<double> & v, ifstream & f) {
    std::string line;
    getline(f, line);
    lean_assert(line == "vector_start");
    do {
        getline(f, line);
        if (line == "vector_end") break;
        auto r = split_and_trim(line);
        unsigned i = atoi(r[0].c_str());
        double val = atof(r[1].c_str());
        v.set_value(val, i);
        std::cout << "setting value " << i << " = " << val << std::endl;
    } while (true);
}

void check_lu_from_file(std::string lufile_name) {
    ifstream f(lufile_name);
    if (!f.is_open()) {
        std::cout << "cannot open file " << lufile_name << std::endl;
    }
    unsigned m, n;
    get_matrix_dimensions(f, m, n);
    std::cout << "init matrix " << m << " by " << n << std::endl;
    static_matrix<double, double> A(m, n);
    read_rows(A, f);
    vector<unsigned> basis;
    read_basis(basis, f);
    indexed_vector<double> v(m);
    //    read_indexed_vector(v, f);
    f.close();
    vector<int> basis_heading;
    lp_settings settings;
    vector<unsigned> non_basic_columns;
    lu<double, double> lsuhl(A, basis, basis_heading, settings, non_basic_columns);
    vector<double> d(A.row_count());
#ifdef LEAN_DEBUG
    lp_settings::ddd = 1;
#endif
    unsigned entering = 26;
    lsuhl.solve_Bd(entering, d, v);
#ifdef LEAN_DEBUG
    auto B = get_B(lsuhl);
    vector<double>  a(m);
    A.copy_column_to_vector(entering, a);
    vector<double> cd(d);
    B.apply_from_left(cd, settings);
    lean_assert(vectors_are_equal(cd , a));
#endif
}

void test_square_dense_submatrix() {
    std::cout << "testing square_dense_submatrix" << std::endl;
    unsigned parent_dim = 7;
    sparse_matrix<double, double> parent(parent_dim);
    fill_matrix(parent);
    unsigned index_start = 3;
    square_dense_submatrix<double, double> d;
    d.init(&parent, index_start);
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            d[i][j] = i*3+j*2;
#ifdef LEAN_DEBUG
    unsigned dim = parent_dim - index_start;
    dense_matrix<double, double> m(dim, dim);
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            m[i-index_start][j-index_start] = d[i][j];
    print_matrix(m, std::cout);
#endif
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            d[i][j] = d[j][i];
#ifdef LEAN_DEBUG
    for (unsigned i = index_start; i < parent_dim; i++)
        for (unsigned j = index_start; j < parent_dim; j++)
            m[i-index_start][j-index_start] = d[i][j];

    print_matrix(m, std::cout);
    std::cout << std::endl;
#endif
}

int main(int argn, char * const * argv) {
    initialize_util_module();
    initialize_numerics_module();
    int ret;
    argument_parser args_parser(argn, argv);
    setup_args_parser(args_parser);
    if (!args_parser.parse()) {
        std::cout << args_parser.m_error_message << std::endl;
        std::cout << args_parser.usage_string();
        ret = 1;
        return finalize(ret);
    }
    std::cout << "the options are " << std::endl;
    args_parser.print();
    std::string lufile = args_parser.get_option_value("--checklu");
    if (lufile.size()) {
        check_lu_from_file(lufile);
        return finalize(0);
    }

#ifdef LEAN_DEBUG
    if (args_parser.option_is_used("--test_swaps")) {
        sparse_matrix<double, double> m(10);
        fill_matrix(m);
        test_swap_rows_with_permutation(m);
        test_swap_cols_with_permutation(m);
        return finalize(0);
    }
#endif
    if (args_parser.option_is_used("--test_file_directory")) {
        test_files_from_directory(args_parser.get_option_value("--test_file_directory"), args_parser);
        return finalize(0);
    }
    if (args_parser.option_is_used("--lar")){
        std::cout <<"calling test_lar_solver" << std::endl;
        test_lar_solver(args_parser);
        return finalize(0);
    }
    std::string file_list = args_parser.get_option_value("--filelist");
    if (file_list.size() > 0) {
        for (std::string fn : get_file_names_from_file_list(file_list))
            solve_mps(fn, args_parser);
        return finalize(0);
    }

    if (args_parser.option_is_used("-tbq")) {
        test_binary_priority_queue();
        ret = 0;
        return finalize(ret);
    }

#ifdef LEAN_DEBUG
    lp_settings settings;
    update_settings(args_parser, settings);
    if (args_parser.option_is_used("--test_lu")) {
        test_lu(settings);
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--test_larger_lu")) {
        test_larger_lu(settings);
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--test_larger_lu_with_holes")) {
        test_larger_lu_with_holes(settings);
        ret = 0;
        return finalize(ret);
    }
#endif

    if (args_parser.option_is_used("--test_lp_0")) {
        test_lp_0();
        ret = 0;
        return finalize(ret);
    }


    unsigned max_iters;
    unsigned time_limit;
    get_time_limit_and_max_iters_from_parser(args_parser, time_limit, max_iters);
    bool dual = args_parser.option_is_used("--dual");
    bool solve_for_rational = args_parser.option_is_used("--mpq");
    std::string file_name = args_parser.get_option_value("--file");
    if (file_name.size() > 0) {
        solve_mps(file_name, args_parser.option_is_used("--min"), max_iters, time_limit, solve_for_rational, dual, args_parser.option_is_used("--compare_with_primal"), args_parser);
        ret = 0;
        return finalize(ret);
    }

    if (args_parser.option_is_used("--solve_some_mps")) {
        solve_some_mps(args_parser);
        ret = 0;
        return finalize(ret);
    }
    //  lean::ccc = 0;
    return finalize(0);
    test_init_U();
    test_replace_column();
#ifdef LEAN_DEBUG
    test_perm_apply_reverse_from_right();
    sparse_matrix_with_permutaions_test();
    test_dense_matrix();
    test_swap_operations();
    test_permutations();
    test_pivot_like_swaps_and_pivot();
#endif
    tst1();
    std::cout<< "done with LP tests\n";
    return finalize(has_violations() ? 1 : 0);
}
