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
#include "util/lp/lar_core_solver.cpp"
template lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::lar_core_solver(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::column_type, std::allocator<lean::column_type> >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<unsigned int, std::allocator<unsigned int> >&, lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, lean::lp_settings&, std::unordered_map<unsigned int, std::string, std::hash<unsigned int>, std::equal_to<unsigned int>, std::allocator<std::pair<unsigned int const, std::string> > >&, std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > >&, std::vector<lean::mpq, std::allocator<lean::mpq> >&);
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::solve();
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::prefix();
template void lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::print_column_info(unsigned int, std::ostream & out);
#ifdef LEAN_DEBUG
template lean::numeric_pair<lean::mpq> lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::get_deb_inf();
#endif
template bool lean::lar_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::is_empty() const;
