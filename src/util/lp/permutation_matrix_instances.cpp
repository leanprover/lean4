/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <memory>
#include <vector>
#include "util/lp/permutation_matrix.cpp"
#include "util/lp/numeric_pair.h"
template void lean::permutation_matrix<double, double>::apply_from_right(std::vector<double, std::allocator<double> >&);
template void lean::permutation_matrix<double, double>::init(unsigned int);
template bool lean::permutation_matrix<double, double>::is_identity() const;
template void lean::permutation_matrix<double, double>::multiply_by_permutation_from_left(lean::permutation_matrix<double, double>&);
template void lean::permutation_matrix<double, double>::multiply_by_permutation_reverse_from_left(lean::permutation_matrix<double, double>&);
template void lean::permutation_matrix<double, double>::multiply_by_reverse_from_right(lean::permutation_matrix<double, double>&);
template lean::permutation_matrix<double, double>::permutation_matrix(unsigned int, std::vector<unsigned int, std::allocator<unsigned int> > const&);
template void lean::permutation_matrix<double, double>::transpose_from_left(unsigned int, unsigned int);
template void lean::permutation_matrix<float, float>::apply_from_right(std::vector<float, std::allocator<float> >&);
template lean::permutation_matrix<float, float>::permutation_matrix(unsigned int);
template void lean::permutation_matrix<float, float>::transpose_from_left(unsigned int, unsigned int);
template void lean::permutation_matrix<float, float>::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_from_right(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template bool lean::permutation_matrix<lean::mpq, lean::mpq>::is_identity() const;
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_permutation_from_left(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_permutation_from_right(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_permutation_reverse_from_left(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_reverse_from_right(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template lean::permutation_matrix<lean::mpq, lean::mpq>::permutation_matrix(unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::transpose_from_left(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_right(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template bool lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::is_identity() const;
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_permutation_from_left(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_permutation_from_right(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_permutation_reverse_from_left(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_reverse_from_right(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::permutation_matrix(unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::transpose_from_left(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<double, double>::apply_from_left_perm<double>(lean::indexed_vector<double>&, lean::lp_settings&);
template void lean::permutation_matrix<double, double>::apply_from_left_perm<double>(std::vector<double, std::allocator<double> >&);
template void lean::permutation_matrix<double, double>::apply_reverse_from_left<double>(lean::indexed_vector<double>&);
template void lean::permutation_matrix<double, double>::apply_reverse_from_left<double>(std::vector<double, std::allocator<double> >&);
template void lean::permutation_matrix<double, double>::apply_reverse_from_right<double>(std::vector<double, std::allocator<double> >&);
template void lean::permutation_matrix<double, double>::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<float, float>::apply_from_left_perm<float>(lean::indexed_vector<float>&, lean::lp_settings&);
template void lean::permutation_matrix<float, float>::apply_from_left_perm<float>(std::vector<float, std::allocator<float> >&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_from_left_perm<lean::mpq>(lean::indexed_vector<lean::mpq>&, lean::lp_settings&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_from_left_perm<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_left<lean::mpq>(lean::indexed_vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_left<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_right<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_left_perm<lean::mpq>(lean::indexed_vector<lean::mpq>&, lean::lp_settings&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_left_perm<lean::numeric_pair<lean::mpq> >(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_left<lean::mpq>(lean::indexed_vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_left<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_left<lean::numeric_pair<lean::mpq> >(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_right<lean::mpq>(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::permutation_matrix<double, double>::multiply_by_permutation_from_right(lean::permutation_matrix<double, double>&);

#ifdef LEAN_DEBUG
template bool lean::permutation_generator<double, double>::move_next();
template lean::permutation_generator<double, double>::permutation_generator(unsigned int);
#endif
template lean::permutation_matrix<double, double>::permutation_matrix(unsigned int);
