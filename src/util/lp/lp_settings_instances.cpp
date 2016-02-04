/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include <memory>
#include "util/lp/lp_settings.cpp"
template bool lean::vectors_are_equal<double>(std::vector<double, std::allocator<double> > const&, std::vector<double, std::allocator<double> > const&);
