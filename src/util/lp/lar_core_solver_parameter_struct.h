/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include <string>
#include "util/lp/lp_settings.h"

namespace lean {
template <typename T, typename X>
struct lar_core_solver_parameter_struct {
std::vector<X> m_x; // the solution
std::vector<column_type> m_column_types;
std::vector<X> m_low_bounds;
std::vector<X> m_upper_bounds;
std::vector<unsigned> m_basis;
static_matrix<T, X> m_A;
lp_settings m_settings;
std::unordered_map<unsigned, std::string> m_column_names;
};
}
