/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/numerics/mpq.h"
#include "util/numerics/double.h"
#include "interval/interval_def.h"

namespace lean {
template class interval<mpq>;
template class interval<double>;
}

void print(lean::interval<lean::mpq> const & i) { std::cout << i << std::endl; }
void print(lean::interval<double> const & i) { std::cout << i << std::endl; }
