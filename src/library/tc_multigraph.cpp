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
static name * g_fun_sink  = nullptr;
static name * g_sort_sink = nullptr;
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

    pair<environment, list<name>> operator()(name const & src, name const & edge, name const & tgt) {
        buffer<std::tuple<name, name, name>> new_edges;
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
        buffer<std::tuple<name, name, name>> new_back_edges;
        new_back_edges.append(new_edges);
        if (auto succs = m_graph.m_successors.find(tgt)) {
            for (pair<name, name> const & p : *succs) {
                if (src == p.second)
                    continue; // avoid loops
                name new_e = compose(src, edge, p.first, p.second);
                new_edges.emplace_back(src, new_e, p.second);
                for (auto const & back_edge : new_back_edges) {
                    name bsrc, bedge, btgt;
                    std::tie(bsrc, bedge, btgt) = back_edge;
                    if (bsrc != p.second)
                        continue;
                    name new_e = compose(bsrc, bedge, p.first, p.second);
                    new_edges.emplace_back(bsrc, new_e, p.second);
                }
            }
        }
        buffer<name> new_cnsts;
        add_core(src, edge, tgt);
        for (auto const & new_edge : new_edges) {
            name nsrc, nedge, ntgt;
            std::tie(nsrc, nedge, ntgt) = new_edge;
            add_core(nsrc, nedge, ntgt);
            new_cnsts.push_back(nedge);
        }
        return mk_pair(m_env, to_list(new_cnsts));
    }
};

/** \brief Return true iff args contains Var(0), Var(1), ..., Var(args.size() - 1) */
static bool check_var_args(buffer<expr> const & args) {
    buffer<bool> found;
    found.resize(args.size(), false);
    for (unsigned i = 0; i < args.size(); i++) {
        if (!is_var(args[i]))
            return false;
        unsigned idx = var_idx(args[i]);
        if (idx >= args.size() || found[idx])
            return false;
        found[idx] = true;
    }
    return true;
}

/** \brief Return true iff param_id(levels[i]) == level_params[i] */
static bool check_levels(levels ls, level_param_names ps) {
    while (!is_nil(ls) && !is_nil(ps)) {
        if (!is_param(head(ls)))
            return false;
        if (param_id(head(ls)) != head(ps))
            return false;
        ls = tail(ls);
        ps = tail(ps);
    }
    return is_nil(ls) && is_nil(ps);
}

static void throw_ex(name const & k, name const & e) {
    throw exception(sstream() << "invalid " << k << ", type of '" << e
                    << "' does not match any of the allowed expected types for " << k << "s\n"
                    << "  Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), D t_1 ... t_m\n"
                    << "  Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), Type\n"
                    << "  Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), A -> B");
}

pair<name, name> tc_multigraph::validate(environment const & env, name const & e, unsigned num_args) {
    declaration const & d = env.get(e);
    expr type = d.get_type();
    for (unsigned i = 0; i < num_args; i++) {
        if (!is_pi(type)) {
            throw_ex(m_kind, e);
        }
        type = binding_body(type);
    }
    if (!is_pi(type)) {
        throw_ex(m_kind, e);
    }
    buffer<expr> args;
    expr const & C = get_app_args(binding_domain(type), args);
    if (!is_constant(C) || !check_levels(const_levels(C), d.get_univ_params()) || !check_var_args(args)) {
        throw_ex(m_kind, e);
    }
    name src = const_name(C);
    type = binding_body(type);
    name tgt;
    if (is_sort(type)) {
        tgt = *g_sort_sink;
    } else if (is_pi(type)) {
        tgt = *g_fun_sink;
    } else {
        expr const & D = get_app_fn(type);
        if (is_constant(D)) {
            tgt = const_name(D);
        } else {
            throw_ex(m_kind, e);
        }
    }
    if (src == tgt) {
        throw_ex(m_kind, e);
    }
    return mk_pair(src, tgt);
}

pair<environment, list<name>> tc_multigraph::add(environment const & env, name const & e, unsigned num_args) {
    auto src_tgt = validate(env, e, num_args);
    return add_edge_fn(env, *this)(src_tgt.first, e, src_tgt.second);
}

pair<environment, list<name>> tc_multigraph::add(environment const & env, name const & e) {
    declaration const & d = env.get(e);
    unsigned n = get_arity(d.get_type());
    if (n == 0)
        throw_ex(m_kind, e);
    return add(env, e, n-1);
}

void tc_multigraph::add1(environment const & env, name const & e, unsigned num_args) {
    auto src_tgt = validate(env, e, num_args);
    return add_edge_fn(env, *this).add_core(src_tgt.first, e, src_tgt.second);
}

void tc_multigraph::add1(environment const & env, name const & e) {
    declaration const & d = env.get(e);
    unsigned n = get_arity(d.get_type());
    if (n == 0)
        throw_ex(m_kind, e);
    return add1(env, e, n-1);
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

bool tc_multigraph::is_fun_sink(name const & c) {
    return c == *g_fun_sink;
}

bool tc_multigraph::is_sort_sink(name const & c) {
    return c == *g_sort_sink;
}

void initialize_tc_multigraph() {
    name p = name::mk_internal_unique_name();
    g_fun_sink  = new name(p, "Fun");
    g_sort_sink = new name(p, "Sort");
}

void finalize_tc_multigraph() {
    delete g_fun_sink;
    delete g_sort_sink;
}
}
