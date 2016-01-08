/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/debug.h"
#include "util/pair.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include "util/lp/lp_settings.h"
namespace lean {
template <typename T>
void zero_vector(T * t, unsigned size) {
    while (size-- > 0) { // it can be made faster by copying big chunks
        t[size] = numeric_traits<T>::zero();
    }
}

template <typename T>
T abs (T const & v) { return v >= zero_of_type<T>() ? v : -v; }


template <typename T>
class sparse_vector_iterator; // forward definition

template <typename T>
class sparse_vector {
public:
    std::vector<pair<unsigned, T>>  m_data;
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
        for (auto & t : m_data) {
            t.second /= a;
        }
    }

    unsigned size() const {
        return m_data.size();
    }

    friend sparse_vector_iterator<T>;
};

template <typename T>
class sparse_vector_iterator {
    typedef typename std::vector<pair<unsigned, T>>::iterator p_it;
    p_it m_it;
    p_it m_end;
public:
    sparse_vector_iterator(sparse_vector<T> & s_v) : m_it(s_v.m_data.begin()),
                                                     m_end(s_v.m_data.end()) {
    }

    bool done() {
        return m_it == m_end;
    }

    void move() {
        m_it++;
    }

    unsigned index() {
        return m_it->first;
    }

    const T & value() const {
        return m_it->second;
    }
};
}
