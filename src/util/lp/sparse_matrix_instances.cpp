/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include <memory>
#include "util/lp/lu.h"
#include "util/lp/sparse_matrix.cpp"
namespace lean {
template double sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, std::vector<double> const&) const;
template void sparse_matrix<double, double>::add_new_element(unsigned int, unsigned int, double);
template void sparse_matrix<double, double>::divide_row_by_constant(unsigned int, double&, lp_settings&);
template void sparse_matrix<double, double>::fill_eta_matrix(unsigned int, eta_matrix<double, double>**);
template const double & sparse_matrix<double, double>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<double, double>::get_number_of_nonzeroes() const;
template unsigned sparse_matrix<double, double>::get_number_of_nonzeroes_below_row(unsigned int) const;
template bool sparse_matrix<double, double>::get_pivot_for_column(unsigned int&, unsigned int&, double const&, unsigned int);
template unsigned sparse_matrix<double, double>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<double, double>::pivot_row_to_row(unsigned int, double, unsigned int, lp_settings&);
template bool sparse_matrix<double, double>::pivot_with_eta(unsigned int, eta_matrix<double, double>*, lp_settings&);
template void sparse_matrix<double, double>::prepare_for_factorization();
template void sparse_matrix<double, double>::remove_element(std::vector<indexed_value<double> >&, indexed_value<double>&);
template void     sparse_matrix<double, double>::replace_column(unsigned int, indexed_vector<double>&, lp_settings&);
template void     sparse_matrix<double, double>::set(unsigned int, unsigned int, double);
template void     sparse_matrix<double, double>::set_max_in_row(std::vector<indexed_value<double> >&);
template bool sparse_matrix<double, double>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<double>&, lp_settings&);
template bool sparse_matrix<double, double>::shorten_active_matrix(unsigned int, eta_matrix<double, double>*);
template void sparse_matrix<double, double>::solve_y_U(std::vector<double>&) const;
template sparse_matrix<double, double>::sparse_matrix(static_matrix<double, double> const&, std::vector<unsigned int>&);
template sparse_matrix<double, double>::sparse_matrix(unsigned int);
template float const & sparse_matrix<float, float>::get(unsigned int, unsigned int) const;
template bool sparse_matrix<float, float>::pivot_row_to_row(unsigned int, float, unsigned int, lp_settings&);
template void  sparse_matrix<float, float>::replace_column(unsigned int, indexed_vector<float>&, lp_settings&);
template void     sparse_matrix<float, float>::set(unsigned int, unsigned int, float);
template sparse_matrix<float, float>::sparse_matrix(unsigned int);
template void     sparse_matrix<mpq, mpq>::add_new_element(unsigned int, unsigned int, mpq);
template void     sparse_matrix<mpq, mpq>::divide_row_by_constant(unsigned int, mpq&, lp_settings&);
template void     sparse_matrix<mpq, mpq>::fill_eta_matrix(unsigned int, eta_matrix<mpq, mpq>**);
template  mpq const & sparse_matrix<mpq, mpq>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<mpq, mpq>::get_number_of_nonzeroes() const;
template unsigned sparse_matrix<mpq, mpq>::get_number_of_nonzeroes_below_row(unsigned int) const;
template bool sparse_matrix<mpq, mpq>::get_pivot_for_column(unsigned int&, unsigned int&, mpq const&, unsigned int);
template unsigned sparse_matrix<mpq, mpq>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<mpq, mpq>::pivot_with_eta(unsigned int, eta_matrix<mpq, mpq>*, lp_settings&);
template void  sparse_matrix<mpq, mpq>::prepare_for_factorization();
template void   sparse_matrix<mpq, mpq>::remove_element(std::vector<indexed_value<mpq>> &, indexed_value<mpq>&);
template void     sparse_matrix<mpq, mpq>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     sparse_matrix<mpq, mpq>::set_max_in_row(std::vector<indexed_value<mpq>>&);
template bool sparse_matrix<mpq, mpq>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool sparse_matrix<mpq, mpq>::shorten_active_matrix(unsigned int, eta_matrix<mpq, mpq>*);
template void     sparse_matrix<mpq, mpq>::solve_y_U(std::vector<mpq>&) const;
template sparse_matrix<mpq, mpq>::sparse_matrix(static_matrix<mpq, mpq> const&, std::vector<unsigned int>&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::add_new_element(unsigned int, unsigned int, mpq);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::divide_row_by_constant(unsigned int, mpq&, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::fill_eta_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >**);
template const mpq & sparse_matrix<mpq, numeric_pair<mpq>>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::get_number_of_nonzeroes() const;
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::get_number_of_nonzeroes_below_row(unsigned int) const;
template bool sparse_matrix<mpq, numeric_pair<mpq>>::get_pivot_for_column(unsigned int&, unsigned int&, mpq const&, unsigned int);
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::pivot_with_eta(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::prepare_for_factorization();
template void     sparse_matrix<mpq, numeric_pair<mpq>>::remove_element(std::vector<indexed_value<mpq>>&, indexed_value<mpq>&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::set_max_in_row(std::vector<indexed_value<mpq>>&);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool     sparse_matrix<mpq, numeric_pair<mpq>>::shorten_active_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::solve_y_U(std::vector<mpq>&) const;
template sparse_matrix<mpq, numeric_pair<mpq>>::sparse_matrix(static_matrix<mpq, numeric_pair<mpq> > const&, std::vector<unsigned int>&);
template void sparse_matrix<double, double>::double_solve_U_y<double>(std::vector<double>&);
template void sparse_matrix<mpq, mpq>::double_solve_U_y<mpq>(std::vector<mpq>&);
template void sparse_matrix<mpq, numeric_pair<mpq>>::double_solve_U_y<mpq>(std::vector<mpq>&);
template void sparse_matrix<mpq, numeric_pair<mpq> >::double_solve_U_y<numeric_pair<mpq> >(std::vector<numeric_pair<mpq>>&);

/////////////////////
/*
  template void lu<double, double>::create_initial_factorization();
  template void lu<mpq, mpq>::create_initial_factorization();
  template void lu<mpq, mpq>::replace_column(unsigned int, mpq, indexed_vector<mpq>&);
  template void lu<mpq, numeric_pair<mpq> >::create_initial_factorization();
  template void lu<mpq, numeric_pair<mpq> >::replace_column(unsigned int, mpq, indexed_vector<mpq>&);
  template void lu<double, double>::init_vector_w(unsigned int, indexed_vector<double>&);
  template void lu<mpq, mpq>::find_error_of_yB(std::vector<mpq, std::allocator<mpq> >&, std::vector<mpq, std::allocator<mpq> > const&);
  template void lu<mpq, mpq>::init_vector_w(unsigned int, indexed_vector<mpq>&);
  template void lu<mpq, numeric_pair<mpq> >::find_error_of_yB(std::vector<mpq, std::allocator<mpq> >&, std::vector<mpq, std::allocator<mpq> > const&);
  template void lu<mpq, numeric_pair<mpq> >::init_vector_w(unsigned int, indexed_vector<mpq>&);
  template void lu<double, double>::find_error_of_yB(std::vector<double, std::allocator<double> >&, std::vector<double, std::allocator<double> > const&);
  #ifdef LEAN_DEBUG
  template void print_matrix<double, double>(static_matrix<double, double>&);
  #endif
*/
#ifdef LEAN_DEBUG
template bool sparse_matrix<double, double>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool sparse_matrix<mpq, mpq>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
#endif
#ifdef LEAN_DEBUG
template bool sparse_matrix<mpq, numeric_pair<mpq> >::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
#endif
}
