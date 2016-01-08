/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/

#pragma once
#include <vector>
#include "util/debug.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include <string>
#include "util/lp/sparse_vector.h"
#include <iomanip>
namespace lean {
template <typename T>
void print_vector(const T * t, unsigned l) {
    for (unsigned i = 0; i < l; i++)
        std::cout << t[i] << " ";
    std::cout << std::endl;
}

template <typename T>
void print_vector(const std::vector<T> & t) {
    for (unsigned i = 0; i < t.size(); i++)
        std::cout << t[i] << " ";
    std::cout << std::endl;
}

template <typename T>
void print_vector(const buffer<T> & t) {
    for (unsigned i = 0; i < t.size(); i++)
        std::cout << t[i] << " ";
    std::cout << std::endl;
}

template <typename T>
void print_sparse_vector(const std::vector<T> & t) {
    for (unsigned i = 0; i < t.size(); i++) {
        if (is_zero(t[i]))continue;
        std::cout << "[" << i << "] = " << t[i] << ", ";
    }
    std::cout << std::endl;
}

void print_vector(const std::vector<mpq> & t) {
    for (unsigned i = 0; i < t.size(); i++)
        std::cout << t[i].get_double() << std::setprecision(3) << " ";
    std::cout << std::endl;
}

template <typename T>
class indexed_vector {
public:
    // m_index points to non-zero elements of m_data
    buffer<T> m_data;
    std::vector<unsigned> m_index;
    indexed_vector(unsigned data_size) {
        m_data.resize(data_size, numeric_traits<T>::zero());
    }

    void resize(unsigned data_size) {
        m_index.clear();
        m_data.resize(data_size, numeric_traits<T>::zero());
    }

    unsigned data_size() const {
        return m_data.size();
    }

    unsigned size() {
        return m_index.size();
    }

    void set_value(T value, unsigned index) {
        m_data[index] = value;
        m_index.push_back(index);
    }

    void clear() {
        for (unsigned i : m_index) {
            m_data[i] = numeric_traits<T>::zero();
        }
        m_index.clear();
    }

    void clear_all() {
        unsigned i = m_data.size();
        while (i--)  m_data[i] = numeric_traits<T>::zero();

        m_index.clear();
    }

    const T& operator[] (unsigned i) const {
        return m_data[i];
    }

    T& operator[] (unsigned i)  {
        return m_data[i];
    }


    void erase_from_index(unsigned j) {
        auto it = std::find(m_index.begin(), m_index.end(), j);
        if (it != m_index.end()) m_index.erase(it);
    }

#ifdef LEAN_DEBUG
    bool is_OK() const {
        int size = 0;
        for (unsigned i = 0; i < m_data.size(); i++) {
            if (!is_zero(m_data[i])) {
                if (std::find(m_index.begin(), m_index.end(), i) == m_index.end())
                    return false;
                size++;
            }
        }
        return size == m_index.size();
    }
    void print() {
        std::cout << "m_index " << std::endl;
        for (unsigned i = 0; i < m_index.size(); i++) {
            std::cout << m_index[i] << " ";
        }
        std::cout << std::endl;
        print_vector(m_data);
    }
#endif
};
}
