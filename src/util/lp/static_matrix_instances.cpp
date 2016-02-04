/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include <memory>
#include <set>
#include "util/lp/static_matrix.cpp"
#include "util/lp/lp_core_solver_base.h"
#include "util/lp/lp_dual_core_solver.h"
#include "util/lp/lp_dual_simplex.h"
#include "util/lp/lp_primal_core_solver.h"
#include "util/lp/scaler.h"
#include "util/lp/lar_solver.h"
namespace lean {
template double static_matrix<double, double>::dot_product_with_row<double>(unsigned int, std::vector<double, std::allocator<double> > const&);
template mpq static_matrix<mpq, mpq>::dot_product_with_row<mpq>(unsigned int, std::vector<mpq, std::allocator<mpq> > const&);
template numeric_pair<mpq> static_matrix<mpq, numeric_pair<mpq> >::dot_product_with_row<numeric_pair<mpq> >(unsigned int, std::vector<numeric_pair<mpq>, std::allocator<numeric_pair<mpq> > > const&);
template void static_matrix<double, double>::add_column_to_vector(double const&, unsigned int, double*) const;
template void static_matrix<double, double>::add_columns_at_the_end(unsigned int);
template void static_matrix<double, double>::clear();
#ifdef LEAN_DEBUG
template bool static_matrix<double, double>::col_val_equal_to_row_val() const;
#endif
template void static_matrix<double, double>::copy_column_to_vector(unsigned int, indexed_vector<double>&) const;
template void static_matrix<double, double>::copy_column_to_vector(unsigned int, std::vector<double, std::allocator<double> >&) const;
template void static_matrix<double, double>::divide_row_by_constant(unsigned int, double const&);
template double static_matrix<double, double>::dot_product_with_column(std::vector<double, std::allocator<double> > const&, unsigned int) const;
template double static_matrix<double, double>::get_balance() const;
template std::set<pair<unsigned, unsigned>> static_matrix<double, double>::get_domain();
template double static_matrix<double, double>::get_elem(unsigned int, unsigned int) const;
template double static_matrix<double, double>::get_max_abs_in_column(unsigned int) const;
template double static_matrix<double, double>::get_min_abs_in_column(unsigned int) const;
template double static_matrix<double, double>::get_min_abs_in_row(unsigned int) const;
template void static_matrix<double, double>::init_empty_matrix(unsigned int, unsigned int);
template void static_matrix<double, double>::init_row_columns(unsigned int, unsigned int);
template static_matrix<double, double>::ref & static_matrix<double, double>::ref::operator=(double const&);
template void static_matrix<double, double>::scale_column(unsigned int, double const&);
template void static_matrix<double, double>::scale_row(unsigned int, double const&);
template void static_matrix<double, double>::set(unsigned int, unsigned int, double const&);
template static_matrix<double, double>::static_matrix(unsigned int, unsigned int);
template void static_matrix<mpq, mpq>::add_column_to_vector(mpq const&, unsigned int, mpq*) const;
template void static_matrix<mpq, mpq>::add_columns_at_the_end(unsigned int);
#ifdef LEAN_DEBUG
template bool static_matrix<mpq, mpq>::col_val_equal_to_row_val() const;
#endif
template void static_matrix<mpq, mpq>::copy_column_to_vector(unsigned int, indexed_vector<mpq>&) const;
template void static_matrix<mpq, mpq>::divide_row_by_constant(unsigned int, mpq const&);
template mpq static_matrix<mpq, mpq>::dot_product_with_column(std::vector<mpq, std::allocator<mpq> > const&, unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_balance() const;
template mpq static_matrix<mpq, mpq>::get_elem(unsigned int, unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_max_abs_in_column(unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_max_abs_in_row(unsigned int) const;
template double static_matrix<double, double>::get_max_abs_in_row(unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_min_abs_in_column(unsigned int) const;
template mpq static_matrix<mpq, mpq>::get_min_abs_in_row(unsigned int) const;
template void static_matrix<mpq, mpq>::init_row_columns(unsigned int, unsigned int);
template static_matrix<mpq, mpq>::ref& static_matrix<mpq, mpq>::ref::operator=(mpq const&);
template void static_matrix<mpq, mpq>::scale_column(unsigned int, mpq const&);
template void static_matrix<mpq, mpq>::scale_row(unsigned int, mpq const&);
template void static_matrix<mpq, mpq>::set(unsigned int, unsigned int, mpq const&);

template static_matrix<mpq, mpq>::static_matrix(unsigned int, unsigned int);
#ifdef LEAN_DEBUG
template bool static_matrix<mpq, numeric_pair<mpq> >::col_val_equal_to_row_val() const;
#endif
template void static_matrix<mpq, numeric_pair<mpq> >::copy_column_to_vector(unsigned int, indexed_vector<mpq>&) const;
template mpq static_matrix<mpq, numeric_pair<mpq> >::dot_product_with_column(std::vector<mpq, std::allocator<mpq> > const&, unsigned int) const;
template mpq static_matrix<mpq, numeric_pair<mpq> >::get_elem(unsigned int, unsigned int) const;
template void static_matrix<mpq, numeric_pair<mpq> >::init_empty_matrix(unsigned int, unsigned int);
template void static_matrix<mpq, numeric_pair<mpq> >::set(unsigned int, unsigned int, mpq const&);
}
