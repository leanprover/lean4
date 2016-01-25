/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#ifdef LEAN_DEBUG
#include "util/lp/matrix.cpp"
template void lean::print_matrix<double, double>(lean::matrix<double, double> const&, std::ostream & out);
template bool lean::matrix<double, double>::is_equal(lean::matrix<double, double> const&);
#endif
