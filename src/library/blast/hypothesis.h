/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rc.h"
#include "util/rb_map.h"
#include "library/blast/expr.h"

namespace lean {
namespace blast {
class hypothesis;
class branch;
class state;

typedef unsigned                        hypothesis_idx;
typedef rb_tree<unsigned, unsigned_cmp> hypothesis_idx_set;
typedef list<unsigned>                  hypothesis_idx_list;
typedef buffer<unsigned>                hypothesis_idx_buffer;
template<typename T>
using hypothesis_idx_map = typename lean::rb_map<unsigned, T, unsigned_cmp>;

class hypothesis {
    friend class state;
    name               m_name;         // for pretty printing
    unsigned           m_dead:1;
    unsigned           m_dep_depth;    // dependency depth
    unsigned           m_proof_depth;  // proof depth when the hypothesis was created
    hypothesis_idx_set m_deps;         // hypotheses used by the type and/or value of this hypothesis.
    expr               m_self;
    expr               m_type;
    optional<expr>     m_value;        // justification for this object.
    // Remark: if blast::is_local(m_value) is true, then the hypothesis is an assumption
public:
    hypothesis():m_dead(false), m_dep_depth(0) {}
    name const & get_name() const { return m_name; }
    bool is_dead() const { return m_dead; }
    unsigned get_dep_depth() const { return m_dep_depth; }
    unsigned get_proof_depth() const { return m_proof_depth; }
    hypothesis_idx_set const & get_backward_deps() const { return m_deps; }
    expr const & get_self() const { return m_self; }
    expr const & get_type() const { return m_type; }
    optional<expr> const & get_value() const { return m_value; }
    /** \brief Return true iff this hypothesis depends on \c h. */
    bool depends_on(expr const & h) const { return m_deps.contains(href_index(h)); }
    bool is_assumption() const { return !m_value || is_local_non_href(*m_value); }
};

class hypothesis_idx_buffer_set {
    friend class state;
    hypothesis_idx_buffer m_buffer;
    hypothesis_idx_set    m_set;
public:
    hypothesis_idx_buffer_set() {}
    hypothesis_idx_buffer_set(hypothesis_idx_buffer const & b) {
        for (auto hidx : b)
            insert(hidx);
    }

    void insert(hypothesis_idx h) {
        if (!m_set.contains(h)) {
            m_set.insert(h);
            m_buffer.push_back(h);
        }
    }
    unsigned size() const { return m_buffer.size(); }
    bool empty() const { return m_buffer.empty(); }
    hypothesis_idx_buffer const & as_buffer() const {
        return m_buffer;
    }
    hypothesis_idx_set const & as_set() const {
        return m_set;
    }
};
}}
