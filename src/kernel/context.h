/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/list.h"
#include "kernel/expr.h"

namespace lean {
/**
   \brief An element of the Lean context.
   \see context
*/
class context_entry {
    name     m_name;
    expr     m_domain;
    expr     m_body;
public:
    context_entry(name const & n, expr const & d, expr const & b):m_name(n), m_domain(d), m_body(b) {}
    context_entry(name const & n, expr const & d):m_name(n), m_domain(d) {}
    name const & get_name() const   { return m_name; }
    expr const & get_domain() const { return m_domain; }
    expr const & get_body() const   { return m_body; }
};

/**
   \brief A context is essentially a mapping from free-variables to types (and definition/body).
*/
class context {
    list<context_entry> m_list;
    explicit context(list<context_entry> const & l):m_list(l) {}
public:
    context() {}
    context(context const & c, name const & n, expr const & d):m_list(context_entry(n,d), c.m_list) {}
    context(context const & c, name const & n, expr const & d, expr const & b):m_list(context_entry(n,d,b), c.m_list) {}
    context_entry const & lookup(unsigned vidx) const;
    std::pair<context_entry const &, context> lookup_ext(unsigned vidx) const;
    bool is_empty() const { return is_nil(m_list); }
    unsigned size() const { return length(m_list); }
    typedef list<context_entry>::iterator iterator;
    iterator begin() const { return m_list.begin(); }
    iterator end() const { return m_list.end(); }
    friend bool is_eqp(context const & c1, context const & c2) { return is_eqp(c1.m_list, c2.m_list); }
};

/**
   \brief Return the context entry for the free variable with de
   Bruijn index \c i, and the context for this entry.
*/
inline std::pair<context_entry const &, context> lookup_ext(context const & c, unsigned i) { return c.lookup_ext(i); }
/**
   \brief Return the context entry for the free variable with de
   Bruijn index \c i.
*/
inline context_entry const & lookup(context const & c, unsigned i) { return c.lookup(i); }
inline context extend(context const & c, name const & n, expr const & d, expr const & b) { return context(c, n, d, b); }
inline context extend(context const & c, name const & n, expr const & d) { return context(c, n, d); }
inline bool is_empty(context const & c) { return c.is_empty(); }
}
