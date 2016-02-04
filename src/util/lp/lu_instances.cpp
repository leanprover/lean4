/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include <vector>
#include "util/lp/lu.cpp"
template double lean::dot_product<double, double>(std::vector<double, std::allocator<double> > const&, std::vector<double, std::allocator<double> > const&, unsigned int);
template void lean::lu<double, double>::change_basis(unsigned int, unsigned int);
template lean::lu<double, double>::lu(lean::static_matrix<double, double> const&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<int, std::allocator<int> >&, lean::lp_settings&, std::vector<unsigned int, std::allocator<unsigned int> >&);
template void lean::lu<double, double>::push_matrix_to_tail(lean::tail_matrix<double, double>*);
template void lean::lu<double, double>::replace_column(unsigned int, double, lean::indexed_vector<double>&);
template void lean::lu<double, double>::restore_basis_change(unsigned int, unsigned int);
template void lean::lu<double, double>::solve_Bd(unsigned int, std::vector<double, std::allocator<double> >&, lean::indexed_vector<double>&);
template lean::lu<double, double>::~lu();
template void lean::lu<lean::mpq, lean::mpq>::change_basis(unsigned int, unsigned int);
template void lean::lu<lean::mpq, lean::mpq>::push_matrix_to_tail(lean::tail_matrix<lean::mpq, lean::mpq>*);
template void lean::lu<lean::mpq, lean::mpq>::restore_basis_change(unsigned int, unsigned int);
template void lean::lu<lean::mpq, lean::mpq>::solve_Bd(unsigned int, std::vector<lean::mpq, std::allocator<lean::mpq> >&, lean::indexed_vector<lean::mpq>&);
template lean::lu<lean::mpq, lean::mpq>::~lu();
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::change_basis(unsigned int, unsigned int);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::push_matrix_to_tail(lean::tail_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >*);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::restore_basis_change(unsigned int, unsigned int);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd(unsigned int, std::vector<lean::mpq, std::allocator<lean::mpq> >&, lean::indexed_vector<lean::mpq>&);
template lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::~lu();
template lean::mpq lean::dot_product<lean::mpq, lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> > const&, std::vector<lean::mpq, std::allocator<lean::mpq> > const&, unsigned int);
template void lean::init_factorization<double, double>(lean::lu<double, double>*&, lean::static_matrix<double, double>&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<int, std::allocator<int> >&, lean::lp_settings&, std::vector<unsigned int, std::allocator<unsigned int> >&);
template void lean::init_factorization<lean::mpq, lean::mpq>(lean::lu<lean::mpq, lean::mpq>*&, lean::static_matrix<lean::mpq, lean::mpq>&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<int, std::allocator<int> >&, lean::lp_settings&, std::vector<unsigned int, std::allocator<unsigned int> >&);
template void lean::init_factorization<lean::mpq, lean::numeric_pair<lean::mpq> >(lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >*&, lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<int, std::allocator<int> >&, lean::lp_settings&, std::vector<unsigned int, std::allocator<unsigned int> >&);
#ifdef LEAN_DEBUG
template void lean::print_matrix<double, double>(lean::sparse_matrix<double, double>&, std::ostream & out);
template void lean::print_matrix<float, float>(lean::sparse_matrix<float, float>&, std::ostream & out);
template void lean::print_matrix<double, double>(lean::static_matrix<double, double>&, std::ostream & out);
template bool lean::lu<double, double>::is_correct();
template lean::dense_matrix<double, double> lean::get_B<double, double>(lean::lu<double, double>&);
#endif
template void lean::lu<lean::mpq, lean::mpq>::solve_yB(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lu<double, double>::solve_yB(std::vector<double, std::allocator<double> >&);
template void lean::lu<lean::mpq, lean::mpq>::solve_By(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lu<double, double>::solve_By(std::vector<double, std::allocator<double> >&);
template void lean::lu<lean::mpq, lean::mpq>::replace_column(unsigned int, lean::mpq, lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::replace_column(unsigned int, lean::mpq, lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_By(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::lu<double, double>::init_vector_w(unsigned int, lean::indexed_vector<double>&);
template lean::numeric_pair<lean::mpq> lean::dot_product<lean::mpq, lean::numeric_pair<lean::mpq> >(std::vector<lean::mpq, std::allocator<lean::mpq> > const&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > > const&, unsigned int);
template bool lean::lu<double, double>::pivot_the_row(int); // NOLINT
