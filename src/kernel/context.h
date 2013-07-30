/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "list.h"

namespace lean {
class context_entry {
    name  m_name;
    expr  m_type;
    expr  m_body;
public:
    context_entry(name const & n, expr const & t, expr const & b):m_name(n), m_type(t), m_body(b) {}
    context_entry(expr const & t, expr const & b):m_type(t), m_body(b) {}
    explicit context_entry(expr const & t):m_type(t) {}
    ~context_entry() {}
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
    expr const & get_body() const { return m_body; }
};
typedef list<context_entry> context;
context extend(context const & c, context_entry const & e) { return cons(e, c); }
}
