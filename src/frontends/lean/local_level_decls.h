/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_map.h"
#include "kernel/level.h"

namespace lean {
class local_level_decls {
    name_map<level>    m_decls;
    name_map<unsigned> m_idxs;
    unsigned           m_counter;
public:
    local_level_decls():m_counter(1) {}
    local_level_decls(local_level_decls const & d):m_decls(d.m_decls), m_idxs(d.m_idxs), m_counter(d.m_counter) {}
    void insert(name const & k, level const & v) {
        m_decls.insert(k, v);
        m_idxs.insert(k, m_counter);
        m_counter++;
    }
    level const * find(name const & k) const { return m_decls.find(k); }
    bool contains(name const & k) const { return m_decls.contains(k); }
    bool empty() const { return m_decls.empty(); }
    unsigned find_idx(name const & k) const {
        if (auto r = m_idxs.find(k))
            return *r;
        else
            return 0;
    }
    void for_each(std::function<void(name const &, level const & l)> const & fn) {
        m_decls.for_each(fn);
    }
};
}
