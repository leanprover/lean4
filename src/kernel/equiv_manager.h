/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/expr_maps.h"

namespace lean {
class equiv_manager {
    typedef unsigned node_ref;

    struct node {
        node_ref m_parent;
        unsigned m_rank;
    };

    std::vector<node>  m_nodes;
    expr_map<node_ref> m_to_node;
    bool               m_use_hash;

    node_ref mk_node();
    node_ref find(node_ref n);
    void merge(node_ref n1, node_ref n2);
    node_ref to_node(expr const & e);
    bool is_equiv_core(expr const & e1, expr const & e2);
public:
    equiv_manager():m_use_hash(false) {}
    bool is_equiv(expr const & e1, expr const & e2, bool use_hash = false);
    void add_equiv(expr const & e1, expr const & e2);
};
}
