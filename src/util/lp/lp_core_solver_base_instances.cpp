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
#include "util/lp/lp_core_solver_base.cpp"
template bool lean::lp_core_solver_base<double, double>::A_mult_x_is_off();
template bool lean::lp_core_solver_base<double, double>::basis_heading_is_correct();
template void lean::lp_core_solver_base<double, double>::calculate_pivot_row_of_B_1(unsigned int);
template void lean::lp_core_solver_base<double, double>::calculate_pivot_row_when_pivot_row_of_B1_is_ready();
template bool lean::lp_core_solver_base<double, double>::column_is_dual_feasible(unsigned int) const;
template void lean::lp_core_solver_base<double, double>::fill_reduced_costs_from_m_y_by_rows();
template bool lean::lp_core_solver_base<double, double>::find_x_by_solving();
template lean::non_basic_column_value_position lean::lp_core_solver_base<double, double>::get_non_basic_column_value_position(unsigned int);
template void lean::lp_core_solver_base<double, double>::init_reduced_costs_for_one_iteration();
template lean::lp_core_solver_base<double, double>::lp_core_solver_base(lean::static_matrix<double, double>&, std::vector<double, std::allocator<double> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&, lean::lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&, std::vector<lean::column_type, std::allocator<lean::column_type> >&, std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> >&);

template bool lean::lp_core_solver_base<double, double>::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(std::string, unsigned int);
template void lean::lp_core_solver_base<double, double>::restore_x(unsigned int, double const&);
template void lean::lp_core_solver_base<double, double>::set_non_basic_x_to_correct_bounds();
template void lean::lp_core_solver_base<double, double>::snap_xN_to_bounds_and_free_columns_to_zeroes();
template void lean::lp_core_solver_base<double, double>::solve_Ax_eq_b();
template void lean::lp_core_solver_base<double, double>::solve_Bd(unsigned int);
template void lean::lp_core_solver_base<double, double>::solve_yB(std::vector<double, std::allocator<double> >&);
template bool lean::lp_core_solver_base<double, double>::update_basis_and_x(int, int, double const&);
template void lean::lp_core_solver_base<double, double>::update_x(unsigned int, double);
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::A_mult_x_is_off();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::basis_heading_is_correct();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::calculate_pivot_row_of_B_1(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::calculate_pivot_row_when_pivot_row_of_B1_is_ready();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::column_is_dual_feasible(unsigned int) const;
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::fill_reduced_costs_from_m_y_by_rows();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::find_x_by_solving();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::init_reduced_costs_for_one_iteration();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(std::string, unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::restore_x(unsigned int, lean::mpq const&);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::set_non_basic_x_to_correct_bounds();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::solve_Ax_eq_b();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::solve_Bd(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::solve_yB(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::update_basis_and_x(int, int, lean::mpq const&);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::update_x(unsigned int, lean::mpq);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::calculate_pivot_row_of_B_1(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::calculate_pivot_row_when_pivot_row_of_B1_is_ready();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init_basis_heading();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init_reduced_costs_for_one_iteration();
template lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::lp_core_solver_base(lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, lean::lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&, std::vector<lean::column_type, std::allocator<lean::column_type> >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::print_statistics_with_cost_and_check_that_the_time_is_over(unsigned int, lean::numeric_pair<lean::mpq>);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::snap_xN_to_bounds();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd(unsigned int);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::update_basis_and_x(int, int, lean::numeric_pair<lean::mpq> const&);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::update_x(unsigned int, lean::numeric_pair<lean::mpq>);
template lean::lp_core_solver_base<lean::mpq, lean::mpq>::lp_core_solver_base(lean::static_matrix<lean::mpq, lean::mpq>&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<unsigned int, std::allocator<unsigned int> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, lean::lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > > const&, std::vector<lean::column_type, std::allocator<lean::column_type> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::print_statistics_with_iterations_and_check_that_the_time_is_over(unsigned int);
template std::string lean::lp_core_solver_base<double, double>::column_name(unsigned int) const;
template void lean::lp_core_solver_base<double, double>::pretty_print(std::ostream & out);
template void lean::lp_core_solver_base<double, double>::restore_state(double*, double*);
template void lean::lp_core_solver_base<double, double>::save_state(double*, double*);
template std::string lean::lp_core_solver_base<lean::mpq, lean::mpq>::column_name(unsigned int) const;
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::pretty_print(std::ostream & out);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::restore_state(lean::mpq*, lean::mpq*);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::save_state(lean::mpq*, lean::mpq*);
template std::string lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::column_name(unsigned int) const;
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::pretty_print(std::ostream & out);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::restore_state(lean::mpq*, lean::mpq*);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::save_state(lean::mpq*, lean::mpq*);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB(std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lp_core_solver_base<double, double>::init_lu();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::init_lu();
template int lean::lp_core_solver_base<double, double>::pivots_in_column_and_row_are_different(int, int) const;
template int lean::lp_core_solver_base<lean::mpq, lean::mpq>::pivots_in_column_and_row_are_different(int, int) const;
