/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include <utility>
#include <functional>
#include <vector>
#include "util/name.h"
#include "util/hash.h"
#include "util/name_map.h"
#include "util/optional.h"

namespace lean {
/**
   \brief Store the set of universe constraints.

   It is based on Floyd-Warshall all-pairs shortest path algorithm.
*/
class universe_constraints {
    typedef std::pair<name, int> edge;
    typedef std::vector<edge> edges;
    typedef name_map<edges> node_to_edges;
    typedef std::pair<name, name> name_pair;
    struct name_pair_hash_fn {
        unsigned operator()(name_pair const & p) const { return hash(p.first.hash(), p.second.hash()); }
    };
    typedef std::unordered_map<name_pair, int, name_pair_hash_fn, std::equal_to<name_pair>> distances;
    node_to_edges m_incoming_edges;
    node_to_edges m_outgoing_edges;
    distances     m_distances;
public:
    /**
       \brief Add a new variable.

       \pre The variables does not exist in this set of constraints.
    */
    void add_var(name const & n);
    /**
       \brief Return true iff this set of constraints contains the variable n.
       That is, it was added using add_var.
    */
    bool contains(name const & n) const;
    /** \brief Return true iff n1 >= n2 + k is implied by this set of constraints. */
    bool is_implied(name const & n1, name const & n2, int k) const;
    /** \brief Return true iff n1 < n2 + k is not implied by this set of constraints. */
    bool is_consistent(name const & n1, name const & n2, int k) const;
    /**
       \brief Return true iff the constraint n1 >= n2 + k produces an integer overflow when added
       to the set of constraints.
    */
    bool overflows(name const & n1, name const & n2, int k) const;
    /**
        \brief Add new constraint n1 >= n2 + k.

        \pre is_consistent(n1, n2, k)
        \pre contains(n1)
        \pre contains(n2)
    */
    void add_constraint(name const & n1, name const & n2, int k);
    /**
       \brief Return the "distance" between n1 and n2.
       That is, the best k s.t. n1 >= n2 + k is implied by this set of constraints
       but n1 >= n2 + k + i is not for any i > 0.

       If there is no such k, then return none.
    */
    optional<int> get_distance(name const & n1, name const & n2) const;
};
}
