/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/numeric_pair.h"
#include "util/lp/core_solver_pretty_printer.cpp"
template lean::core_solver_pretty_printer<double, double>::core_solver_pretty_printer(lean::lp_core_solver_base<double, double> &, std::ostream & out);
template void lean::core_solver_pretty_printer<double, double>::print();
template lean::core_solver_pretty_printer<double, double>::~core_solver_pretty_printer();
template lean::core_solver_pretty_printer<lean::mpq, lean::mpq>::core_solver_pretty_printer(lean::lp_core_solver_base<lean::mpq, lean::mpq> &, std::ostream & out);
template void lean::core_solver_pretty_printer<lean::mpq, lean::mpq>::print();
template lean::core_solver_pretty_printer<lean::mpq, lean::mpq>::~core_solver_pretty_printer();
template lean::core_solver_pretty_printer<lean::mpq, lean::numeric_pair<lean::mpq> >::core_solver_pretty_printer(lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> > &, std::ostream & out);
template lean::core_solver_pretty_printer<lean::mpq, lean::numeric_pair<lean::mpq> >::~core_solver_pretty_printer();
template void lean::core_solver_pretty_printer<lean::mpq, lean::numeric_pair<lean::mpq> >::print();
