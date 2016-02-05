/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include "util/lp/indexed_vector.h"
namespace lean {

template <typename T>
void print_vector(const std::vector<T> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++)
        out << t[i] << " ";
    out << std::endl;
}

template <typename T>
void print_vector(const buffer<T> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++)
        out << t[i] << " ";
    out << std::endl;
}

template <typename T>
void print_sparse_vector(const std::vector<T> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++) {
        if (is_zero(t[i]))continue;
        out << "[" << i << "] = " << t[i] << ", ";
    }
    out << std::endl;
}

void print_vector(const std::vector<mpq> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++)
        out << t[i].get_double() << std::setprecision(3) << " ";
    out << std::endl;
}

template <typename T>
void indexed_vector<T>::resize(unsigned data_size) {
    m_index.clear();
    m_data.resize(data_size, numeric_traits<T>::zero());
}

template <typename T>
void indexed_vector<T>::set_value(T value, unsigned index) {
    m_data[index] = value;
    m_index.push_back(index);
}

template <typename T>
void indexed_vector<T>::clear() {
    for (unsigned i : m_index)
        m_data[i] = numeric_traits<T>::zero();
    m_index.clear();
}
template <typename T>
void indexed_vector<T>::clear_all() {
    unsigned i = m_data.size();
    while (i--)  m_data[i] = numeric_traits<T>::zero();
    m_index.clear();
}
template <typename T>
void indexed_vector<T>::erase_from_index(unsigned j) {
    auto it = std::find(m_index.begin(), m_index.end(), j);
    if (it != m_index.end()) m_index.erase(it);
}

#ifdef LEAN_DEBUG
template <typename T>
bool indexed_vector<T>::is_OK() const {
    unsigned size = 0;
    for (unsigned i = 0; i < m_data.size(); i++) {
        if (!is_zero(m_data[i])) {
            if (std::find(m_index.begin(), m_index.end(), i) == m_index.end())
                return false;
            size++;
        }
    }
    return size == m_index.size();
}
template <typename T>
void indexed_vector<T>::print(std::ostream & out) {
    out << "m_index " << std::endl;
    for (unsigned i = 0; i < m_index.size(); i++) {
        out << m_index[i] << " ";
    }
    out << std::endl;
    print_vector(m_data, out);
}
#endif

}
