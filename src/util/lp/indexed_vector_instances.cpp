/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#include "util/lp/indexed_vector.cpp"
namespace lean {
template void indexed_vector<double>::clear();
template void indexed_vector<double>::clear_all();
template void indexed_vector<double>::erase_from_index(unsigned int);
template void indexed_vector<double>::set_value(double, unsigned int);
template void indexed_vector<float>::set_value(float, unsigned int);
template void indexed_vector<mpq>::clear();
template void indexed_vector<mpq>::clear_all();
template void indexed_vector<mpq>::erase_from_index(unsigned int);
template void indexed_vector<mpq>::resize(unsigned int);
template void indexed_vector<mpq>::set_value(mpq, unsigned int);
#ifdef LEAN_DEBUG
template bool indexed_vector<double>::is_OK() const;
template bool lean::indexed_vector<mpq>::is_OK() const;
#endif
}
