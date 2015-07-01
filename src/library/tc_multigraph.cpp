/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "library/tc_multigraph.h"
#include "library/composition_manager.h"
#include "library/util.h"

namespace lean {
struct add_edge_fn {
    environment      m_env;
    type_checker_ptr m_tc;
    tc_multigraph &  m_graph;

    add_edge_fn(environment const & env, tc_multigraph & g):
        m_env(env), m_tc(new type_checker(env)), m_graph(g) {}

    // Return true iff the types of constants c1 and c2 are equal.
    bool is_def_eq(name const & c1, name const & c2) {
        if (c1 == c2)
            return true;
        declaration const & d1 = m_env.get(c1);
        declaration const & d2 = m_env.get(c2);
        if (d1.get_num_univ_params() != d2.get_num_univ_params())
            return false;
        return m_tc->is_def_eq(d1.get_type(), d2.get_type()).first;
    }

    // Erase edges that are definitionally equal to edge
    void erase_def_eqs(name const & src, name const & edge, name const & tgt) {
        buffer<name> to_delete;
        for (auto const & p : m_graph.get_successors(src)) {
            if (p.second == tgt) {
                if (is_def_eq(p.first, edge))
                    to_delete.push_back(p.first);
            }
        }
        for (name const & e : to_delete)
            m_graph.erase(e);
    }

    template<typename Val>
    static void insert_maplist(name_map<list<Val>> & m, name const & k, Val const & v) {
        if (auto it = m.find(k)) {
            m.insert(k, cons(v, filter(*it, [&](Val const & v2) { return v2 != v; })));
        } else {
            m.insert(k, list<Val>(v));
        }
    }

    void add_core(name const & src, name const & edge, name const & tgt) {
        erase_def_eqs(src, edge, tgt);
        insert_maplist(m_graph.m_successors, src, mk_pair(edge, tgt));
        insert_maplist(m_graph.m_predecessors, tgt, src);
        m_graph.m_edges.insert(edge, src);
    }


    static name compose_name_core(name const & src, name const & tgt) {
        return src + name("to") + tgt;
    }

    static name compose_name(name const & p, name const & src, name const & tgt) {
        if (is_prefix_of(p, tgt))
            return compose_name_core(src, tgt.replace_prefix(p, name()));
        else if (p.is_atomic())
            return compose_name_core(src, tgt);
        else
            return compose_name(p.get_prefix(), src, tgt);
    }

    static name compose_name(name const & src, name const & tgt) {
        if (src.is_atomic())
            return compose_name_core(src, tgt);
        else
            return compose_name(src.get_prefix(), src, tgt);
    }

    name compose(name const & src, name const & e1, name const & e2, name const & tgt) {
        name n = compose_name(src, tgt);
        pair<environment, name> env_e = ::lean::compose(m_env, *m_tc, e2, e1, optional<name>(n));
        m_env = env_e.first;
        return env_e.second;
    }

    pair<environment, list<tc_edge>> operator()(name const & src, name const & edge, name const & tgt) {
        buffer<tc_edge> new_edges;
        if (auto preds = m_graph.m_predecessors.find(src)) {
            for (name const & pred : *preds) {
                if (pred == tgt)
                    continue; // avoid loops
                if (auto pred_succ = m_graph.m_successors.find(pred)) {
                    for (pair<name, name> const & p : *pred_succ) {
                        if (p.second != src)
                            continue;
                        name new_e = compose(pred, p.first, edge, tgt);
                        new_edges.emplace_back(pred, new_e, tgt);
                    }
                }
            }
        }
        m_tc.reset(new type_checker(m_env)); // update to reflect new constants in the environment
        buffer<tc_edge> new_back_edges;
        new_back_edges.append(new_edges);
        if (auto succs = m_graph.m_successors.find(tgt)) {
            for (pair<name, name> const & p : *succs) {
                if (src == p.second)
                    continue; // avoid loops
                name new_e = compose(src, edge, p.first, p.second);
                new_edges.emplace_back(src, new_e, p.second);
                for (auto const & back_edge : new_back_edges) {
                    if (back_edge.m_from != p.second)
                        continue;
                    name new_e = compose(back_edge.m_from, back_edge.m_cnst, p.first, p.second);
                    new_edges.emplace_back(back_edge.m_from, new_e, p.second);
                }
            }
        }
        return mk_pair(m_env, to_list(new_edges));
    }
};

pair<environment, list<tc_edge>> tc_multigraph::add(environment const & env, name const & src, name const & e, name const & tgt) {
    return add_edge_fn(env, *this)(src, e, tgt);
}

void tc_multigraph::add1(environment const & env, name const & src, name const & e, name const & tgt) {
    return add_edge_fn(env, *this).add_core(src, e, tgt);
}

void tc_multigraph::erase(name const & e) {
    auto src = m_edges.find(e);
    if (!src)
        return;
    auto succ_lst  = m_successors.find(*src);
    lean_assert(succ_lst);
    name tgt;
    list<pair<name, name>> new_succ_lst = filter(*succ_lst, [&](pair<name, name> const & p) {
            if (p.first == e) {
                lean_assert(tgt.is_anonymous());
                tgt = p.second;
                return false;
            } else {
                return true;
            }
        });
    lean_assert(!tgt.is_anonymous());
    m_successors.insert(*src, new_succ_lst);
    if (std::all_of(new_succ_lst.begin(), new_succ_lst.end(), [&](pair<name, name> const & p) {
                return p.second != tgt;
            })) {
        // e is the last edge from src to tgt
        auto pred_lst = m_predecessors.find(tgt);
        lean_assert(pred_lst);
        list<name> new_pred_lst = filter(*pred_lst, [&](name const & n) { return n != *src; });
        if (new_pred_lst)
            m_predecessors.insert(tgt, new_pred_lst);
        else
            m_predecessors.erase(tgt);
    }
    m_edges.erase(e);
}

bool tc_multigraph::is_edge(name const & e) const {
    return m_edges.contains(e);
}

bool tc_multigraph::is_node(name const & c) const {
    return m_successors.contains(c) || m_predecessors.contains(c);
}

list<pair<name, name>> tc_multigraph::get_successors(name const & c) const {
    if (auto r = m_successors.find(c))
        return *r;
    else
        return list<pair<name, name>>();
}

list<name> tc_multigraph::get_predecessors(name const & c) const {
    if (auto r = m_predecessors.find(c))
        return *r;
    else
        return list<name>();
}

void tc_multigraph::for_each(std::function<void(name const &, name const &, name const &)> const & fn) const {
    m_successors.for_each([&](name const & from, list<pair<name, name>> const & succs) {
            for (pair<name, name> const & p : succs) {
                fn(from, p.first, p.second);
            }
        });
}
}
