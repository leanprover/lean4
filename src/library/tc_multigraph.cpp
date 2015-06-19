/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tc_multigraph.h"

namespace lean {
pair<environment, list<name>> tc_multigraph::add(environment const & env, name const & e, unsigned num_args) {
    // TODO(Leo)
    return mk_pair(env, list<name>());
}
pair<environment, list<name>> tc_multigraph::add(environment const & env, name const & e) {

}
void tc_multigraph::erase(name const & e) {
    auto src = m_edges.find(e);
    if (!src)
        return;
    auto succ_lst  = m_successors.find(*src);
    lean_assert(it);
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
    m_successors.insert(src, new_succ_lst);
    if (std::all_of(new_succs.begin(), new_succs.end(), [&](pair<name, name> const & p) {
                return p.second != tgt;
            })) {
        // e is the last edge from src to tgt
        auto pred_lst = m_predecessors.find(tgt);
        lean_assert(pred_list);
        list<name> new_pred_lst = filter(*pred_lst, [&](name const & n) { return n != src; });
        m_predecessors.insert(tgt, new_pred_lst);
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
}
