/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include <utility>
#include "util/debug.h"
#include "util/lp/lp_utils.h"
#include "util/lp/lp_settings.h"
namespace lean {

template <typename T>
class sparse_vector {
public:
    std::vector<std::pair<unsigned, T>>  m_data;
    void push_back(unsigned index, T val) {
        m_data.emplace_back(index, val);
    }
#ifdef LEAN_DEBUG
    T operator[] (unsigned i) const {
        for (auto t : m_data) {
            if (t.first == i) return t.second;
        }
        return numeric_traits<T>::zero();
    }
#endif
    void divide(T const & a) {
        lean_assert(!lp_settings::is_eps_small_general(a, 1e-12));
        for (auto & t : m_data) {  t.second /= a; }
    }

    unsigned size() const {
        return m_data.size();
    }
};
}
