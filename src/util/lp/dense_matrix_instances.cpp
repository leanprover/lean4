/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#ifdef LEAN_DEBUG
#include <vector>
#include "util/lp/dense_matrix.cpp"
template lean::dense_matrix<double, double> lean::operator*<double, double>(lean::matrix<double, double>&, lean::matrix<double, double>&);
template void lean::dense_matrix<double, double>::apply_from_left(std::vector<double> &);
template lean::dense_matrix<double, double>::dense_matrix(lean::matrix<double, double> const&);
template lean::dense_matrix<double, double>::dense_matrix(unsigned int, unsigned int);
template lean::dense_matrix<double, double>& lean::dense_matrix<double, double>::operator=(lean::dense_matrix<double, double> const&);
#endif
