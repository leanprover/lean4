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
class state;
class goal;

class justification_cell {
    MK_LEAN_RC();
    unsigned m_idx;
    void dealloc();
public:
    justification_cell();
    virtual ~justification_cell() {}
    virtual expr to_expr(hypothesis const &) const = 0;
    /** \brief Return thread local unique identifier associated with justification object */
    unsigned get_idx() const { return m_idx; }
};

class justification {
    justification_cell * m_ptr;
public:
    justification();
    justification(justification_cell & c);
    justification(justification const & s);
    justification(justification && s);
    ~justification();

    justification & operator=(justification const & s);
    justification & operator=(justification && s);
    expr to_expr(hypothesis const & h) const { return m_ptr->to_expr(h); }
};

typedef rb_tree<unsigned, unsigned_cmp> hypothesis_set;

class hypothesis {
    friend class goal;
    bool           m_active;
    unsigned       m_depth;
    hypothesis_set m_backward_deps;
    hypothesis_set m_forward_deps;
    expr           m_type;
    optional<expr> m_value;
    justification  m_jst;
public:
    hypothesis();
    bool is_active() const { return m_active; }
    unsigned get_depth() const { return m_depth; }
    hypothesis_set const & get_backward_deps() const { return m_backward_deps; }
    hypothesis_set const & get_forward_deps() const { return m_forward_deps; }
    expr const & get_type() const { return m_type; }
    optional<expr> const & get_value() const { return m_value; }
    justification const & get_justification() const { return m_jst; }
};
}
}
