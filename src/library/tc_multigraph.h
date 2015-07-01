/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
struct tc_edge {
    name m_from;
    name m_cnst; // constant representing the edge in the environment
    name m_to;
    tc_edge(name const & from, name const & e, name const & to):
        m_from(from), m_cnst(e), m_to(to) {}
};

/** \brief Transitive closed multigraph */
class tc_multigraph {
    name                             m_kind;
    name_map<list<pair<name, name>>> m_successors;
    name_map<list<name>>             m_predecessors;
    name_map<name>                   m_edges;
    pair<name, name> validate(environment const & env, name const & e, unsigned num_args);
    friend struct add_edge_fn;
public:
    tc_multigraph(name const & kind):m_kind(kind) {}
    /** \brief Add a new edge, and return updated environment, and list of transitive edges added to the graph. */
    pair<environment, list<tc_edge>> add(environment const & env, name const & src, name const & e, name const & tgt);
    void add1(environment const & env, name const & src, name const & e, name const & tgt);
    void erase(name const & e);
    bool is_edge(name const & e) const;
    bool is_node(name const & c) const;
    list<pair<name, name>> get_successors(name const & c) const;
    list<name> get_predecessors(name const & c) const;
    void for_each(std::function<void(name const &, name const &, name const &)> const & fn) const;
};
}
