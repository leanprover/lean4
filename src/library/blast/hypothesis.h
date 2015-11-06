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

typedef rb_tree<unsigned, unsigned_cmp> hypothesis_idx_set;
typedef list<unsigned>                  hypothesis_idx_list;
typedef buffer<unsigned>                hypothesis_idx_buffer;
template<typename T>
using hypothesis_idx_map = typename lean::rb_map<unsigned, T, unsigned_cmp>;

class hypothesis {
    friend class branch;
    name               m_name;     // for pretty printing
    unsigned           m_active:1;
    unsigned           m_depth;
    hypothesis_idx_set m_deps;     // hypotheses used by the type and/or value of this hypothesis.
    expr               m_type;
    expr               m_value;    // justification for this object.
    // Remark: if blast::is_local(m_value) is true, then the hypothesis is an assumption
public:
    hypothesis():m_active(false), m_depth(0) {}
    name const & get_name() const { return m_name; }
    bool is_active() const { return m_active; }
    unsigned get_depth() const { return m_depth; }
    hypothesis_idx_set const & get_backward_deps() const { return m_deps; }
    expr const & get_type() const { return m_type; }
    expr const & get_value() const { return m_value; }
    /** \brief Return true iff this hypothesis depends on \c h. */
    bool depends_on(expr const & h) const { return m_deps.contains(href_index(h)); }
    bool is_assumption() const { return is_local_non_href(m_value); }
};
}}
