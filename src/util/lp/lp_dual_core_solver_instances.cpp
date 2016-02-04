/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include <vector>
#include <functional>
#include "util/lp/lp_dual_core_solver.cpp"
template lean::lp_dual_core_solver<lean::mpq, lean::mpq>::lp_dual_core_solver(lean::static_matrix<lean::mpq, lean::mpq>&, std::vector<bool, std::allocator<bool> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<lean::column_type, std::allocator<lean::column_type> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, lean::lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&);
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::start_with_initial_basis_and_make_it_dual_feasible();
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::solve();
template lean::lp_dual_core_solver<double, double>::lp_dual_core_solver(lean::static_matrix<double, double>&, std::vector<bool, std::allocator<bool> >&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<double, std::allocator<double> >&, std::vector<lean::column_type, std::allocator<lean::column_type> >&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, lean::lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&);
template void lean::lp_dual_core_solver<double, double>::start_with_initial_basis_and_make_it_dual_feasible();
template void lean::lp_dual_core_solver<double, double>::solve();
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::restore_non_basis();
template void lean::lp_dual_core_solver<double, double>::restore_non_basis();
template void lean::lp_dual_core_solver<double, double>::revert_to_previous_basis();
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::revert_to_previous_basis();
