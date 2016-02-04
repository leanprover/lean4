/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include <memory>
#include "util/lp/row_eta_matrix.cpp"
#include "util/lp/lu.h"
namespace lean {
template void row_eta_matrix<double, double>::conjugate_by_permutation(permutation_matrix<double, double>&);
template void row_eta_matrix<mpq, numeric_pair<mpq> >::conjugate_by_permutation(permutation_matrix<mpq, numeric_pair<mpq> >&);
template void row_eta_matrix<mpq, mpq>::conjugate_by_permutation(permutation_matrix<mpq, mpq>&);
#ifdef LEAN_DEBUG
template mpq row_eta_matrix<mpq, mpq>::get_elem(unsigned int, unsigned int) const;
template mpq row_eta_matrix<mpq, numeric_pair<mpq> >::get_elem(unsigned int, unsigned int) const;
template double row_eta_matrix<double, double>::get_elem(unsigned int, unsigned int) const;
#endif
template void row_eta_matrix<mpq, mpq>::apply_from_left(std::vector<mpq, std::allocator<mpq> >&, lp_settings&);
template void row_eta_matrix<mpq, mpq>::apply_from_right(std::vector<mpq, std::allocator<mpq> >&);
template void row_eta_matrix<mpq, numeric_pair<mpq> >::apply_from_left(std::vector<numeric_pair<mpq>, std::allocator<numeric_pair<mpq> > >&, lp_settings&);
template void row_eta_matrix<mpq, numeric_pair<mpq> >::apply_from_right(std::vector<mpq, std::allocator<mpq> >&);
template void row_eta_matrix<double, double>::apply_from_left(std::vector<double, std::allocator<double> >&, lp_settings&);
template void row_eta_matrix<double, double>::apply_from_right(std::vector<double, std::allocator<double> >&);
template void row_eta_matrix<mpq, mpq>::apply_from_left_to_T(indexed_vector<mpq>&, lp_settings&);
template void row_eta_matrix<mpq, mpq>::apply_from_left_local_to_T(indexed_vector<mpq>&, lp_settings&);
template void row_eta_matrix<mpq, numeric_pair<mpq> >::apply_from_left_to_T(indexed_vector<mpq>&, lp_settings&);
template void row_eta_matrix<mpq, numeric_pair<mpq> >::apply_from_left_local_to_T(indexed_vector<mpq>&, lp_settings&);
template void row_eta_matrix<double, double>::apply_from_left_to_T(indexed_vector<double>&, lp_settings&);
template void row_eta_matrix<double, double>::apply_from_left_local_to_T(indexed_vector<double>&, lp_settings&);
}
