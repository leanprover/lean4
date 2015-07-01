/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
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
    pair<environment, list<name>> add(environment const & env, name const & src, name const & e, name const & tgt);
    void add1(environment const & env, name const & src, name const & e, name const & tgt);
    void erase(name const & e);
    bool is_edge(name const & e) const;
    bool is_node(name const & c) const;
    list<pair<name, name>> get_successors(name const & c) const;
    list<name> get_predecessors(name const & c) const;
};
}
