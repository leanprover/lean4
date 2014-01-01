/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/list.h"
#include "util/optional.h"
#include "kernel/expr.h"

namespace lean {
/**
   \brief An element of the Lean context.
   \see context
*/
class context_entry {
    name            m_name;
    optional<expr>  m_domain;
    optional<expr>  m_body;
public:
    context_entry(name const & n, optional<expr> const & d, expr const & b):m_name(n), m_domain(d), m_body(b) {}
    context_entry(name const & n, expr const & d, optional<expr> const & b):m_name(n), m_domain(d), m_body(b) {}
    context_entry(name const & n, expr const & d, expr const & b):m_name(n), m_domain(d), m_body(b) {}
    context_entry(name const & n, expr const & d):m_name(n), m_domain(d) {}
    name const & get_name() const   { return m_name; }
    optional<expr> const & get_domain() const { return m_domain; }
    optional<expr> const & get_body() const   { return m_body; }
    friend bool operator==(context_entry const & e1, context_entry const & e2) { return e1.m_domain == e2.m_domain && e1.m_body == e2.m_body; }
    friend bool operator!=(context_entry const & e1, context_entry const & e2) { return !(e1 == e2); }
};

class metavar_env;

/**
   \brief A context is essentially a mapping from free-variables to types (and definition/body).
*/
class context {
    list<context_entry> m_list;
    explicit context(list<context_entry> const & l):m_list(l) {}
public:
    context() {}
    context(context const & c, name const & n, optional<expr> const & d, expr const & b):m_list(context_entry(n, d, b), c.m_list) {}
    context(context const & c, name const & n, expr const & d, optional<expr> const & b):m_list(context_entry(n, d, b), c.m_list) {}
    context(context const & c, name const & n, expr const & d, expr const & b):m_list(context_entry(n, d, b), c.m_list) {}
    context(context const & c, name const & n, expr const & d):m_list(context_entry(n, d), c.m_list) {}
    context(context const & c, context_entry const & e):m_list(e, c.m_list) {}
    context(unsigned sz, context_entry const * es):context(to_list(es, es + sz)) {}
    context(std::initializer_list<std::pair<char const *, expr const &>> const & l);
    context_entry const & lookup(unsigned vidx) const;
    std::pair<context_entry const &, context> lookup_ext(unsigned vidx) const;
    /** \brief Similar to lookup, but always succeed */
    optional<context_entry> find(unsigned vidx) const;
    bool empty() const { return is_nil(m_list); }
    explicit operator bool() const { return !empty(); }
    unsigned size() const { return length(m_list); }
    typedef list<context_entry>::iterator iterator;
    iterator begin() const { return m_list.begin(); }
    iterator end() const { return m_list.end(); }
    friend bool is_eqp(context const & c1, context const & c2) { return is_eqp(c1.m_list, c2.m_list); }
    /**
       \brief Return a new context where entries at positions >= s are removed.
    */
    context truncate(unsigned s) const;
    /**
       \brief Return a new context where the entries at positions [s, s+n) were removed.

       The free variables in entries [0, s) are lowered.
       That is, if this context is of the form
       [ce_m, ..., ce_{s+n}, ce_{s+n-1}, ..., ce_s, ce_{s-1}, ..., ce_0]
       Then, the resultant context is of the form
       [ce_m, ..., ce_{s+n}, lower(ce_{s-1}, n, n), ..., lower(ce_0, s+n-1, n)]

       \pre size() >= s + n

       If for some i in [0, s), has_free_var(ce_i, s - 1 - i, s + n - 1 - i), then return none.
       That is, the lower operations must be valid.
    */
    optional<context> remove(unsigned s, unsigned n, metavar_env const & menv) const;
    friend bool operator==(context const & ctx1, context const & ctx2) { return ctx1.m_list == ctx2.m_list; }
    friend bool operator!=(context const & ctx1, context const & ctx2) { return !(ctx1 == ctx2); }
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
inline optional<context_entry> find(context const & c, unsigned i) { return c.find(i); }
inline context extend(context const & c, name const & n, optional<expr> const & d, expr const & b) { return context(c, n, d, b); }
inline context extend(context const & c, name const & n, expr const & d, optional<expr> const & b) { return context(c, n, d, b); }
inline context extend(context const & c, name const & n, expr const & d, expr const & b) { return context(c, n, d, b); }
inline context extend(context const & c, name const & n, expr const & d) { return context(c, n, d); }
inline bool empty(context const & c) { return c.empty(); }

std::ostream & operator<<(std::ostream & out, context const & ctx);
}
