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
   \brief A "scoped" map from name to values.

   It also supports the operation \c find_idx that returns "when a declaration was inserted into the map".
*/
template<typename V>
class local_decls {
    typedef rb_map<name, std::pair<V, unsigned>, name_quick_cmp> map;
    typedef list<std::pair<map, unsigned>> scopes;
    map       m_map;
    unsigned  m_counter;
    scopes    m_scopes;
public:
    local_decls():m_counter(1) {}
    local_decls(local_decls const & d):m_map(d.m_map), m_counter(d.m_counter), m_scopes(d.m_scopes) {}
    void insert(name const & k, V const & v) { m_map.insert(k, mk_pair(v, m_counter)); m_counter++; }
    V const * find(name const & k) const { auto it = m_map.find(k); return it ? &(it->first) : nullptr; }
    unsigned find_idx(name const & k) const { auto it = m_map.find(k); return it ? it->second : 0; }
    bool contains(name const & k) const { return m_map.contains(k); }
    void push() { m_scopes = scopes(mk_pair(m_map, m_counter), m_scopes); }
    void pop() {
        lean_assert(!is_nil(m_scopes));
        m_map     = head(m_scopes).first;
        m_counter = head(m_scopes).second;
        m_scopes  = tail(m_scopes);
    }
    struct mk_scope {
        local_decls & m_d;
        mk_scope(local_decls & d):m_d(d) { m_d.push(); }
        ~mk_scope() { m_d.pop(); }
    };
};
}
