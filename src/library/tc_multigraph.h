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
    name_map<list<pair<name, name>>> m_successors;
    name_map<list<name>>             m_predecessors;
    name_map<name>                   m_edges;
public:
    pair<environment, list<name>> add(environment const & env, name const & e, unsigned num_args);
    pair<environment, list<name>> add(environment const & env, name const & e);
    void erase(name const & e);
    bool is_edge(name const & e) const;
    bool is_node(name const & c) const;
    list<pair<name, name>> get_successors(name const & c) const;
    list<name> get_predecessors(name const & c) const;
    static bool is_fun_sink(name const & c) const;
    static bool is_sort_sink(name const & c) const;
};
}
