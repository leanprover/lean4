/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include "util/lp/lar_solver.h"
#include "util/lp/lp_primal_core_solver.cpp"
namespace lean {
    //template void lar_solver::find_solution_signature_with_doubles(lar_solution_signature&);
template void lp_primal_core_solver<double, double>::find_feasible_solution();
template lp_primal_core_solver<double, double>::lp_primal_core_solver(static_matrix<double, double>&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<double, std::allocator<double> >&, std::vector<column_type, std::allocator<column_type> >&, std::vector<double, std::allocator<double> >&, lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&);
template lp_primal_core_solver<double, double>::lp_primal_core_solver(static_matrix<double, double>&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<double, std::allocator<double> >&, std::vector<column_type, std::allocator<column_type> >&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&);

template unsigned lp_primal_core_solver<double, double>::solve();
template lp_primal_core_solver<mpq, mpq>::lp_primal_core_solver(static_matrix<mpq, mpq>&, std::vector<mpq, std::allocator<mpq> >&, std::vector<mpq, std::allocator<mpq> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<mpq, std::allocator<mpq> >&, std::vector<column_type, std::allocator<column_type> >&, std::vector<mpq, std::allocator<mpq> >&, std::vector<mpq, std::allocator<mpq> >&, lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&);
template unsigned lp_primal_core_solver<mpq, mpq>::solve();
    //template void lp_primal_simplex<double, double>::solve_with_total_inf();
    //template void lp_primal_simplex<mpq, mpq>::solve_with_total_inf();
}
