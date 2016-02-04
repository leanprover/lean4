/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <utility>
#include "util/lp/lar_constraints.h"
namespace lean {

lar_constraint::lar_constraint(const buffer<std::pair<mpq, var_index>> & left_side, lconstraint_kind kind, mpq right_side, constraint_index index) :  lar_base_constraint(kind, right_side, index) {
    for (auto & it : left_side) {
        auto r = m_left_side.find(it.second);
        if (r == m_left_side.end()) {
            m_left_side[it.second] = it.first;
        } else {
            r->second += it.first;
        }
    }
}

lar_constraint::lar_constraint(const lar_base_constraint & c): lar_base_constraint(c.m_kind, c.m_right_side, c.m_index) {
    for (auto t : c.get_left_side_coefficients())
        m_left_side.insert(std::make_pair(t.second, t.first));
}


buffer<std::pair<mpq, var_index>> lar_constraint::get_left_side_coefficients() const {
    buffer<std::pair<mpq, var_index>> ret;
    for (auto it : m_left_side) {
        ret.push_back(std::make_pair(it.second, it.first));
    }
    return ret;
}

buffer<std::pair<mpq, var_index>> lar_normalized_constraint::get_left_side_coefficients() const {
    buffer<std::pair<mpq, var_index>> ret;
    for (auto t : m_canonic_left_side->m_coeffs) ret.push_back(t);
    return ret;
}
}






