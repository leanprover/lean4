/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/rb_map.h"
#include "util/name.h"
#include "util/list.h"
#include "util/pair.h"

namespace lean {
/**
   \brief A map from name to values.

   It also supports the operation \c find_idx that returns "when a declaration was inserted into the map".
*/
template<typename V>
class local_decls {
    typedef name_map<pair<V, unsigned>> map;
    typedef list<pair<name, V>> entries;
    map      m_map;
    entries  m_entries;
    unsigned m_counter;
public:
    local_decls():m_counter(1) {}
    local_decls(local_decls const & d):
        m_map(d.m_map), m_entries(d.m_entries), m_counter(d.m_counter) {}
    void insert(name const & k, V const & v) {
        m_map.insert(k, mk_pair(v, m_counter));
        m_entries = cons(mk_pair(k, v), m_entries);
        m_counter++;
    }
    void update(name const & k, V const & v) {
        if (auto it = m_map.find(k)) {
            m_map.insert(k, mk_pair(v, it->second));
        } else {
            lean_unreachable();
        }
    }
    V const * find(name const & k) const { auto it = m_map.find(k); return it ? &(it->first) : nullptr; }
    unsigned find_idx(name const & k) const { auto it = m_map.find(k); return it ? it->second : 0; }
    bool contains(name const & k) const { return m_map.contains(k); }
    entries const & get_entries() const { return m_entries; }
    bool empty() const { return m_map.empty(); }
};
}
