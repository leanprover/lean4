/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/scaler.cpp"
template bool lean::scaler<double, double>::scale();
template bool lean::scaler<lean::mpq, lean::mpq>::scale();
