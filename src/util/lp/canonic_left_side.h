/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <string>
#include <algorithm>
#include <utility>
#include "util/lp/column_info.h"
namespace lean {

enum lconstraint_kind {
    LE = -2, LT = -1 , GE = 2, GT = 1, EQ = 0
};

class lar_normalized_constraint; // forward definition
inline   bool compare(const std::pair<mpq, var_index> & a, const std::pair<mpq, var_index> & b) {
    return a.second < b.second;
}

class canonic_left_side {
public:
    // this index is exposed to the user, this is not the index that points to the row
    unsigned m_row_index = static_cast<unsigned>(-1);
    var_index m_additional_var_index = static_cast<var_index>(-1); // this is the index of the additional variable created for this constraint
    std::vector<std::pair<mpq, var_index>> m_coeffs;
    lar_normalized_constraint * m_low_bound_witness = nullptr;
    lar_normalized_constraint * m_upper_bound_witness = nullptr;

    canonic_left_side(buffer<std::pair<mpq, var_index>> buffer) {
        for (auto it : buffer) {
            if (numeric_traits<mpq>::is_zero(it.first)) continue;
            m_coeffs.push_back(it);
        }

        std::sort(m_coeffs.begin(), m_coeffs.end(), compare);
        normalize();
    }

    unsigned size() const { return static_cast<unsigned>(m_coeffs.size()); }

    void normalize() {
        if (m_coeffs.size() == 0) return;
        auto t = m_coeffs[0].first;
        for (auto & it : m_coeffs)
            it.first /= t;
    }

    bool operator==(const canonic_left_side& a) const {
        if (m_coeffs.size() != a.m_coeffs.size()) return false;
        for (unsigned i = 0; i < m_coeffs.size(); i++) {
            if (m_coeffs[i] != a.m_coeffs[i])
                return false;
        }
        return true;
    }

    std::size_t hash_of_ls() const {
        std::size_t ret = 0;
        std::hash<std::pair<mpq, var_index>> hash_fun;
        for (auto v : m_coeffs) {
            ret |= (hash_fun(v) << 2);
        }
        return ret;
    }
};

struct hash_and_equal_of_canonic_left_side_struct {
    std::size_t operator() (const canonic_left_side* ls) const {
        return ls->hash_of_ls();
    }
    bool operator() (const canonic_left_side* a, const canonic_left_side* b) const {
        return (*a) == (*b);
    }
};
}
