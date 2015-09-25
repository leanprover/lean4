/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rc.h"
#include "util/rb_tree.h"
#include "kernel/expr.h"

namespace lean {
namespace blast {
class hypothesis;
class branch;
class state;

typedef rb_tree<unsigned, unsigned_cmp> hypothesis_set;

class hypothesis {
    friend class branch;
    name           m_name; // for pretty printing
    bool           m_active;
    unsigned       m_depth;
    hypothesis_set m_backward_deps;
    hypothesis_set m_forward_deps;
    expr           m_type;
    optional<expr> m_value;
    optional<expr> m_justification;
public:
    hypothesis():m_active(0), m_depth(0) {}
    bool is_active() const { return m_active; }
    unsigned get_depth() const { return m_depth; }
    hypothesis_set const & get_backward_deps() const { return m_backward_deps; }
    hypothesis_set const & get_forward_deps() const { return m_forward_deps; }
    expr const & get_type() const { return m_type; }
    optional<expr> const & get_value() const { return m_value; }
    optional<expr> const & get_justification() const { return m_justification; }
};
}}
