/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "list.h"

namespace lean {
class context_entry;
typedef list<context_entry> context;
class context_entry {
    name     m_name;
    expr     m_type;
    expr     m_body;
    friend context extend(context const & c, name const & n, expr const & t, expr const & b);
    friend context extend(context const & c, name const & n, expr const & t);
    context_entry(name const & n, expr const & t, expr const & b):m_name(n), m_type(t), m_body(b) {}
    context_entry(name const & n, expr const & t):m_name(n), m_type(t) {}
public:
    ~context_entry() {}
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
    expr const & get_body() const { return m_body; }
};
context const & lookup(context const & c, unsigned i);
inline context extend(context const & c, name const & n, expr const & t, expr const & b) {
    return context(context_entry(n, t, b), c);
}
inline context extend(context const & c, name const & n, expr const & t) {
    return context(context_entry(n, t), c);
}
std::ostream & operator<<(std::ostream & out, context const & c);
}
