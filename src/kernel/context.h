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
    expr     m_domain;
    expr     m_body;
    friend context extend(context const & c, name const & n, expr const & d, expr const & b);
    friend context extend(context const & c, name const & n, expr const & d);
    context_entry(name const & n, expr const & d, expr const & b):m_name(n), m_domain(d), m_body(b) {}
    context_entry(name const & n, expr const & d):m_name(n), m_domain(d) {}
public:
    ~context_entry() {}
    name const & get_name() const   { return m_name; }
    expr const & get_domain() const { return m_domain; }
    expr const & get_body() const   { return m_body; }
};
/**
   \brief Return the context entry for the free variable with de
   Bruijn index \c i, and the context for this entry.
*/
std::pair<context_entry const &, context const &> lookup_ext(context const & c, unsigned i);
/**
   \brief Return the context entry for the free variable with de
   Bruijn index \c i.
*/
context_entry const & lookup(context const & c, unsigned i);

inline context extend(context const & c, name const & n, expr const & d, expr const & b) {
    return context(context_entry(n, d, b), c);
}
inline context extend(context const & c, name const & n, expr const & d) {
    return context(context_entry(n, d), c);
}
inline bool is_empty(context const & c) {
    return is_nil(c);
}
}
