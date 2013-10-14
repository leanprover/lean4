/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include <unordered_map>
#include <utility>

template <class T>
inline void hash_combine(std::size_t & seed, const T & v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

namespace std {
template<typename S, typename T> struct hash<pair<S, T>> {
    inline size_t operator()(const pair<S, T> & v) const {
        size_t seed = 0;
        ::hash_combine(seed, v.first);
        ::hash_combine(seed, v.second);
        return seed;
    }
};
}

namespace lean {
using std::unordered_map;

template <typename T>
class matrix_domain {
    vector<unordered_map<unsigned, void *>> m_domain;
public:
    matrix_domain(unsigned rows) {
        while (rows--) {
            unordered_map<unsigned, void *> t;
            m_domain.push_back(t);
        }
    }
    void * find(unsigned i, unsigned j) const {
        auto & v = m_domain[i];
        auto t = v.find(j);
        if (t == v.end()) {
            return nullptr;
        }
        return t->second;
    }

    void erase(unsigned i, unsigned j) {
        lean_assert(find(i, j) != nullptr);
        m_domain[i].erase(j);
    }

    void insert(unsigned i, unsigned j, void * cell)  {
        lean_assert(m_domain[i].find(j) == m_domain[i].end());
        m_domain[i][j] = cell;
    }

    unsigned size() const {
        unsigned ret = 0;
        for (auto &  t : m_domain) {
            ret += t.size();
        }
        return ret;
    }
};
}
