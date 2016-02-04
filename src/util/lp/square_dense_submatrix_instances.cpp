/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <memory>
#include <vector>
#include "util/lp/square_dense_submatrix.cpp"
template void lean::square_dense_submatrix<double, double>::init(lean::sparse_matrix<double, double>*, unsigned int);
template lean::square_dense_submatrix<double, double>::square_dense_submatrix(lean::sparse_matrix<double, double>*, unsigned int);
template void lean::square_dense_submatrix<double, double>::update_parent_matrix(lean::lp_settings&);
template bool lean::square_dense_submatrix<double, double>::is_L_matrix() const;
template void lean::square_dense_submatrix<double, double>::conjugate_by_permutation(lean::permutation_matrix<double, double>&);
template int lean::square_dense_submatrix<double, double>::find_pivot_column_in_row(unsigned int) const;
template void lean::square_dense_submatrix<double, double>::pivot(unsigned int, lean::lp_settings&);
template lean::square_dense_submatrix<lean::mpq, lean::numeric_pair<lean::mpq> >::square_dense_submatrix(lean::sparse_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >*, unsigned int);
template void lean::square_dense_submatrix<lean::mpq, lean::numeric_pair<lean::mpq> >::update_parent_matrix(lean::lp_settings&);
template bool lean::square_dense_submatrix<lean::mpq, lean::numeric_pair<lean::mpq> >::is_L_matrix() const;
template void lean::square_dense_submatrix<lean::mpq, lean::numeric_pair<lean::mpq> >::conjugate_by_permutation(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template int lean::square_dense_submatrix<lean::mpq, lean::numeric_pair<lean::mpq> >::find_pivot_column_in_row(unsigned int) const;
template void lean::square_dense_submatrix<lean::mpq, lean::numeric_pair<lean::mpq> >::pivot(unsigned int, lean::lp_settings&);
#ifdef LEAN_DEBUG
template double lean::square_dense_submatrix<double, double>::get_elem(unsigned int, unsigned int) const;
#endif
template void lean::square_dense_submatrix<double, double>::apply_from_right(std::vector<double, std::allocator<double> >&);
template void  lean::square_dense_submatrix<double, double>::apply_from_left_local<double>(lean::indexed_vector<double>&, lean::lp_settings&);
template void  lean::square_dense_submatrix<double, double>::apply_from_left_to_vector<double>(std::vector<double, std::allocator<double> >&);
template lean::square_dense_submatrix<lean::mpq, lean::mpq>::square_dense_submatrix(lean::sparse_matrix<lean::mpq, lean::mpq>*, unsigned int);
template void lean::square_dense_submatrix<lean::mpq, lean::mpq>::update_parent_matrix(lean::lp_settings&);
template bool lean::square_dense_submatrix<lean::mpq, lean::mpq>::is_L_matrix() const;
template void lean::square_dense_submatrix<lean::mpq, lean::mpq>::conjugate_by_permutation(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template int lean::square_dense_submatrix<lean::mpq, lean::mpq>::find_pivot_column_in_row(unsigned int) const;
template void lean::square_dense_submatrix<lean::mpq, lean::mpq>::pivot(unsigned int, lean::lp_settings&);
