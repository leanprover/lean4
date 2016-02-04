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

template <typename T> void print_vector(const std::vector<T> & t, std::ostream & out);
template <typename T> void print_vector(const buffer<T> & t, std::ostream & out);
template <typename T> void print_sparse_vector(const std::vector<T> & t, std::ostream & out);

void print_vector(const std::vector<mpq> & t, std::ostream & out);
template <typename T>
class indexed_vector {
public:
    // m_index points to non-zero elements of m_data
    buffer<T> m_data;
    std::vector<unsigned> m_index;
    indexed_vector(unsigned data_size) {
        m_data.resize(data_size, numeric_traits<T>::zero());
    }

    void resize(unsigned data_size);
    unsigned data_size() const {
        return m_data.size();
    }

    unsigned size() {
        return m_index.size();
    }

    void set_value(T value, unsigned index);
    void clear();
    void clear_all();
    const T& operator[] (unsigned i) const {
        return m_data[i];
    }

    T& operator[] (unsigned i)  {
        return m_data[i];
    }


    void erase_from_index(unsigned j);
#ifdef LEAN_DEBUG
    bool is_OK() const;
    void print(std::ostream & out);
#endif
};
}
