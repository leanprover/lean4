/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/pair.h"
#include "util/splay_tree.h"

namespace lean {
/**
   \brief Wrapper for implementing maps using splay trees.
*/
template<typename K, typename T, typename CMP>
class splay_map : public CMP {
    typedef std::pair<K, T> entry;
    struct entry_cmp : public CMP {
        entry_cmp(CMP const & c):CMP(c) {}
        int operator()(entry const & e1, entry const & e2) const { return CMP::operator()(e1.first, e2.first); }
    };
    splay_tree<entry, entry_cmp> m_map;
public:
    splay_map(CMP const & cmp = CMP()):m_map(entry_cmp(cmp)) {}

    void swap(splay_map & m) { m_map.swap(m.m_map); }
    bool empty() const { return m_map.empty(); }
    void clear() { m_map.clear(); }
    bool is_eqp(splay_map const & m) const { return m_map.is_eqp(m); }
    unsigned size() const { return m_map.size(); }
    void insert(K const & k, T const & v) { m_map.insert(mk_pair(k, v)); }
    entry const * find(K const & k) const { return m_map.find(mk_pair(k, T())); }
    bool contains(K const & k) const { return m_map.contains(mk_pair(k, T())); }
    entry const * find_memoize(K const & k) { return m_map.contains(mk_pair(k, T())); }
    void erase(K const & k) { m_map.erase(mk_pair(k, T())); }

    class ref {
        splay_map & m_map;
        K const &   m_key;
    public:
        ref(splay_map & m, K const & k):m_map(m), m_key(k) {}
        ref & operator=(T const & v) { m_map.insert(m_key, v); return *this; }
        operator T const &() {
            entry const * e = m_map.find(m_key);
            if (e) {
                return e->second;
            } else {
                m_map.insert(m_key, T());
                return m_map.find(m_key)->second;
            }
        }
    };

    /**
       \brief Returns a reference to the value that is mapped to a key equivalent to key,
       performing an insertion if such key does not already exist.
    */
    ref operator[](K const & k) { return ref(*this, k); }
};
}
