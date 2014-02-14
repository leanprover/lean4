/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include <unordered_map>
#include <vector>
#include "util/hash.h"
#include "util/safe_arith.h"
#include "kernel/diff_cnstrs.h"

namespace lean {

struct diff_cnstrs::imp {
    typedef int      edge_id;
    static constexpr edge_id null_edge_id = -1;

    struct edge_jst {
        bool m_propagation;
        union {
            justification m_asserted;
            edge_id       m_implied_by;
        };
        edge_jst():m_propagation(false), m_asserted(nullptr) {}
        edge_jst(justification jst):m_propagation(false), m_asserted(jst) {}
        edge_jst(edge_id e_id):m_propagation(true), m_implied_by(e_id) {}
    };

    struct edge {
        node          m_source;
        node          m_target;
        distance      m_distance;
        edge_jst      m_justification;
        edge(node s, node t, distance d, edge_jst const & j):
            m_source(s), m_target(t), m_distance(d), m_justification(j) {}
    };

    enum class trail_kind { MkNode, AddEdge, DisableNode };

    struct trail {
        trail_kind m_kind;
        union {
            edge_id m_old_edge_id;
            node    m_disabled_node; // node that was disabled
        };
        trail(trail_kind k):m_kind(k) {}
    };

    typedef std::pair<node, node> node_pair;
    struct node_pair_hash { unsigned operator()(node_pair const & p) const { return hash(p.first, p.second); } };
    typedef std::unordered_map<std::pair<node, node>, edge_id, node_pair_hash, std::equal_to<node_pair>> distances;
    typedef std::vector<edge_id> edge_ids;

    new_eq_eh             m_eh;
    std::vector<edge>     m_edges;           // vector/trail of all edges
    std::vector<bool>     m_enabled;         // map node      -> bool
    std::vector<edge_ids> m_incoming_edges;  // map node      -> incoming edges
    std::vector<edge_ids> m_outgoing_edges;  // map node      -> outgoing edges
    distances             m_distances;       // map node*node -> edge
    std::vector<trail>    m_trail_stack;     // trail/undo stack
    std::vector<unsigned> m_scopes;

    imp(new_eq_eh const & eh):m_eh(eh) {}

    imp(imp const & s, new_eq_eh const & eh):
        m_eh(eh),
        m_edges(s.m_edges),
        m_enabled(s.m_enabled),
        m_incoming_edges(s.m_incoming_edges),
        m_outgoing_edges(s.m_outgoing_edges),
        m_distances(s.m_distances) {
        // the trail (aka backtracking stack) is not copied
    }

    void push_mk_node_trail() {
        m_trail_stack.push_back(trail(trail_kind::MkNode));
    }

    void push_new_edge_trail(edge_id old_edge = null_edge_id) {
        trail t(trail_kind::AddEdge);
        t.m_old_edge_id = old_edge;
        m_trail_stack.push_back(t);
    }

    void push_disable_node_trail(node n) {
        trail t(trail_kind::DisableNode);
        t.m_disabled_node = n;
        m_trail_stack.push_back(t);
    }

    void undo_mk_node() {
        lean_assert(!m_enabled.empty());
        lean_assert(!m_incoming_edges.empty());
        lean_assert(!m_outgoing_edges.empty());
        lean_assert(m_incoming_edges.back().empty());
        lean_assert(m_outgoing_edges.back().empty());
        m_incoming_edges.pop_back();
        m_outgoing_edges.pop_back();
        m_enabled.pop_back();
    }

    void undo_disable_node(node n) {
        lean_assert(n < m_enabled.size());
        lean_assert(!m_enabled[n]);
        m_enabled[n] = true;
    }

    void undo_add_edge(edge_id old_e_id) {
        lean_assert(!m_edges.empty());
        edge_id e_id = m_edges.size() - 1;
        auto & e     = m_edges.back();
        node s       = e.m_source;
        node t       = e.m_target;
        auto & out   = m_outgoing_edges[s];
        auto & in    = m_incoming_edges[t];
        lean_assert_eq(m_distances[node_pair(s, t)], e_id);
        if (old_e_id == null_edge_id) {
            m_distances.erase(node_pair(s, t));
            in.erase(std::remove(in.begin(), in.end(), e_id), in.end());
            out.erase(std::remove(out.begin(), out.end(), e_id), out.end());
        } else {
            m_distances[node_pair(s, t)] = old_e_id;
            std::replace(in.begin(), in.end(), e_id, old_e_id);
            std::replace(out.begin(), out.end(), e_id, old_e_id);
        }
        m_edges.pop_back();
    }

    void push() {
        m_scopes.push_back(m_trail_stack.size());
    }

    void pop(unsigned num_scopes) {
        unsigned lvl = m_scopes.size();
        lean_assert(num_scopes <= lvl);
        unsigned new_lvl = lvl - num_scopes;
        unsigned old_trail_sz = m_scopes[new_lvl];
        unsigned i = m_trail_stack.size();
        while (i > old_trail_sz) {
            --i;
            trail const & t = m_trail_stack.back();
            switch (t.m_kind) {
            case trail_kind::MkNode:      undo_mk_node();                       break;
            case trail_kind::AddEdge:     undo_add_edge(t.m_old_edge_id);       break;
            case trail_kind::DisableNode: undo_disable_node(t.m_disabled_node); break;
            }
            m_trail_stack.pop_back();
        }
        lean_assert(m_trail_stack.size() == old_trail_sz);
        m_scopes.resize(new_lvl);
    }

    void disable_node(node n) {
        lean_assert(n < m_enabled.size());
        lean_assert(m_enabled[n]);
        m_enabled[n] = false;
        push_disable_node_trail(n);
    }

    bool is_enabled(node n) const {
        lean_assert(n < m_enabled.size());
        return m_enabled[n];
    }

    optional<distance> get_distance(node s, node t) const {
        auto it = m_distances.find(node_pair(s, t));
        if (it == m_distances.end())
            return optional<distance>();
        else
            return optional<distance>(m_edges[it->second].m_distance);
    }

    bool is_implied(node s, node t, distance d) const {
        auto d1 = get_distance(s, t);
        return d1 && *d1 >= d;
    }

    bool is_consistent(node s, node t, distance d) const {
        // we just check if t >= s - d + 1 is not implied
        return !is_implied(t, s, safe_sub(1, d));
    }

    void check_new_eq(edge const & e) {
        if (e.m_distance == 0 && e.m_source != e.m_target) {
            auto d = get_distance(e.m_target, e.m_source);
            if (d && *d == 0) {
                // new implied equality
                m_eh(e.m_source, e.m_target);
            }
        }
    }

    bool add_edge_core(edge const & e) {
        node s  = e.m_source;
        node t  = e.m_target;
        auto it = m_distances.find(node_pair(s, t));
        if (it == m_distances.end()) {
            edge_id e_id = m_edges.size();
            m_edges.push_back(e);
            m_distances[node_pair(s, t)] = e_id;
            m_incoming_edges[t].push_back(e_id);
            m_outgoing_edges[s].push_back(e_id);
            push_new_edge_trail(null_edge_id);
            check_new_eq(e);
            return true;
        } else {
            edge_id old_e_id = it->second;
            distance d       = e.m_distance;
            if (d > m_edges[old_e_id].m_distance) {
                edge_id e_id = m_edges.size();
                m_edges.push_back(e);
                it->second = e_id;
                auto & in  = m_incoming_edges[t];
                auto & out = m_outgoing_edges[s];
                std::replace(in.begin(), in.end(), old_e_id, e_id);
                std::replace(out.begin(), out.end(), old_e_id, e_id);
                push_new_edge_trail(old_e_id);
                check_new_eq(e);
                return true;
            } else {
                return false; // redundant edge
            }
        }
    }

    bool add_edge_core(node s, node t, distance d, edge_jst const & j) {
        return add_edge_core(edge(s, t, d, j));
    }

    node mk_node() {
        node n = m_enabled.size();
        m_enabled.push_back(true);
        m_incoming_edges.push_back(edge_ids());
        m_outgoing_edges.push_back(edge_ids());
        push_mk_node_trail();
        add_edge_core(n, n, 0, edge_jst());
        lean_assert(*get_distance(n, n) == 0);
        return n;
    }

    void add_edge(node s, node t, distance d, justification j) {
        lean_assert(is_enabled(s));
        lean_assert(is_enabled(t));
        lean_assert(is_consistent(s, t, d));
        if (is_implied(s, t, d))
            return; // redundant
        edge_id new_e_id = m_edges.size();
        edge_jst prop_jst(new_e_id);
        buffer<edge> to_add;
        to_add.push_back(edge(s, t, d, edge_jst(j)));
        for (auto in_id : m_incoming_edges[s]) {
            edge & e = m_edges[in_id];
            if (is_enabled(e.m_source) && e.m_source != s)
                to_add.emplace_back(e.m_source, t, safe_add(e.m_distance, d), prop_jst);
        }
        for (auto out_id : m_outgoing_edges[t]) {
            edge & e = m_edges[out_id];
            if (is_enabled(e.m_target) && t != e.m_target)
                to_add.emplace_back(s, e.m_target, safe_add(e.m_distance, d), prop_jst);
        }
        for (auto const & e : to_add) {
            auto old_d = get_distance(e.m_source, e.m_target);
            if (!old_d || e.m_distance > *old_d)
                add_edge_core(e);
        }
    }

    void explain(node s, node t, buffer<justification> & js) const {
        if (s != t) {
            buffer<node_pair> todo;
            todo.push_back(node_pair(s, t));
            while (!todo.empty()) {
                node s         = todo.back().first;
                node t         = todo.back().second;
                edge_id e_id   = m_distances.find(todo.back())->second;
                todo.pop_back();
                edge const & e = m_edges[e_id];
                edge_jst j     = e.m_justification;
                if (!j.m_propagation && j.m_asserted != nullptr) {
                    js.push_back(j.m_asserted);
                } else {
                    edge const & e1 = m_edges[j.m_implied_by];
                    if (e1.m_source != e1.m_target)
                        todo.push_back(node_pair(e1.m_source, e1.m_target));
                    if (s != e1.m_source)
                        todo.push_back(node_pair(s, e1.m_source));
                    if (e1.m_target != t)
                        todo.push_back(node_pair(e1.m_target, t));
                }
            }
        }
    }

    void display(std::ostream & out) const {
        for (node n = 0; n < m_outgoing_edges.size(); n++) {
            if (is_enabled(n)) {
                for (edge_id e_id : m_outgoing_edges[n]) {
                    auto const & e = m_edges[e_id];
                    lean_assert(e.m_source == n);
                    if (e.m_target != n && is_enabled(e.m_target))
                        out << "n" << n << " + " << e.m_distance << " <= n" << e.m_target << "\n";
                }
            }
        }
    }
};

diff_cnstrs::diff_cnstrs(new_eq_eh const & eh):m_ptr(new imp(eh)) {}
diff_cnstrs::diff_cnstrs(diff_cnstrs const & s, new_eq_eh const & eh):m_ptr(new imp(*s.m_ptr, eh)) {}
diff_cnstrs::~diff_cnstrs() {}
diff_cnstrs::node diff_cnstrs::mk_node() { return m_ptr->mk_node(); }
void diff_cnstrs::add_edge(node s, node t, distance d, justification j) { m_ptr->add_edge(s, t, d, j); }
void diff_cnstrs::disable_node(node n) { m_ptr->disable_node(n); }
void diff_cnstrs::push() { m_ptr->push(); }
void diff_cnstrs::pop(unsigned num_scopes) { m_ptr->pop(num_scopes); }
optional<diff_cnstrs::distance> diff_cnstrs::get_distance(node s, node t) const { return m_ptr->get_distance(s, t); }
bool diff_cnstrs::is_enabled(node n) const { return m_ptr->is_enabled(n); }
void diff_cnstrs::explain(node s, node t, buffer<justification> & js) const { m_ptr->explain(s, t, js); }
bool diff_cnstrs::is_implied(node s, node t, distance d) const { return m_ptr->is_implied(s, t, d); }
bool diff_cnstrs::is_consistent(node s, node t, distance d) const { return m_ptr->is_consistent(s, t, d); }
void diff_cnstrs::display(std::ostream & out) const { m_ptr->display(out); }
}
