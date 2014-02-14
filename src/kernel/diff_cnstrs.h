/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "util/optional.h"
#include "util/buffer.h"

namespace lean {
class diff_cnstrs {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    typedef unsigned node;
    /**
       \brief The justifications are "opaque" to this module.
       From the point of view of this module, they are just markers.
    */
    typedef void *   justification;
    typedef int      distance;
    /**
       \brief Event handler for implied equalities.
    */
    typedef std::function<void(node, node)> new_eq_eh;
    /**
       \brief Create an empty set of constraints. The "customer" can provide
       an event handler that will be invoked whenever an equality between two nodes
       is inferred.
    */
    diff_cnstrs(new_eq_eh const & eh = [](node, node) {});
    diff_cnstrs(diff_cnstrs const & s, new_eq_eh const & eh = [](node, node) {});
    ~diff_cnstrs();


    /**
       \brief Create a new node.
    */
    node mk_node();

    /**
       \brief Disable a node created using \c mk_node.

       \remark We cannot add edges between disabled nodes.

       \pre is_enabled(n)
    */
    void disable_node(node n);

    /**
       \brief Return true iff the given node is enabled.
    */
    bool is_enabled(node n) const;

    /**
       \brief Add an edge <tt>s -d-> t</tt> with justification \c j.
       The edge can be viewed as an inequality <tt>s + d <= t</tt>.

       \remark This method assumes that the new edge would not produce
       a "positive cycle". A positive cycle in the graph is an "inconsistency"
       of the form <tt>k <= 0</tt>, where \c k is a positive number.

       \pre is_consistent(s, t, d)
       \pre is_enabled(s)
       \pre is_enabled(t)
    */
    void add_edge(node s, node t, distance d, justification j);

    /**
       \brief Create a backtracking point.
    */
    void push();

    /**
       \brief Restore backtracking point. This method undoes the \c mk_node,
       \c disable_node and \c add_edge operations between
       this call and the matching \c push.
    */
    void pop(unsigned num_scopes = 1);

    /**
       \brief Return the distance between \c s and \c t.
       If the result is none, then the distance is "infinite", i.e.,
       there is no path between \c s and \c t.

       The distance \c d between \c s and \c t can be viewed as
       an inequality <tt>s + d <= t</tt>, and this is the "best"
       inequality implied by the already added edges. By best,
       we mean, forall d1 > d, !is_implied(s, t, d1)
    */
    optional<distance> get_distance(node s, node t) const;

    /**
       \brief Return true iff the already added edges imply
       that distance between \c s and \c t is at least \c d
    */
    bool is_implied(node s, node t, distance d) const;

    /**
       \brief Return true iff by adding the edge s -d-> t we don't
       create a positive cycle.
       This method is equivalent to <tt>!is_implied(t, s, 1-d)</tt>
    */
    bool is_consistent(node s, node t, distance d) const;

    /**
       \brief Return a "justification" for <tt>get_distance(s, t)</tt>.
       The distance is implied by a subset of edges added using
       \c add_edge. This method collect the justification for each one
       of theses edges in \c js.
    */
    void explain(node s, node t, buffer<justification> & js) const;

    /**
       \brief Display the distances between all ones. This used only
       for debugging purposes.
    */
    void display(std::ostream & out) const;
};
}
