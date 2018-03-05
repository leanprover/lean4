/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "util/rb_map.h"
#include "util/memory_pool.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/fun_info.h"
#include "library/discr_tree.h"

namespace lean {
/* Auxiliary expr used to implement insert/erase operations.
   When adding the children of an application into the todo stack,
   we use g_delimiter to indicate where the arguments end.
   For example, suppose the current stack is S, and we want
   to add the children of (f a b). Then, the new stack will
   be [S, *g_delimiter, b, a]
   \remark g_delimiter is an unique expression. */
static expr * g_delimiter = nullptr;

struct discr_tree::node_cmp {
    int operator()(node const & n1, node const & n2) const;
};

void discr_tree::swap(node & n1, node & n2) {
    std::swap(n1.m_ptr, n2.m_ptr);
}

struct discr_tree::edge {
    edge_kind m_kind;
    bool      m_fn;
    name      m_name; // only relevant for Local/Const
    edge(edge_kind k):m_kind(k), m_fn(false) {}
    edge(expr const & e, bool fn) {
        m_fn = fn;
        lean_assert(is_constant(e) || is_local(e));
        if (is_constant(e)) {
            m_kind = edge_kind::Constant;
            m_name = const_name(e);
        } else {
            lean_assert(is_local(e));
            m_kind = edge_kind::Local;
            m_name = mlocal_name(e);
        }
    }
};

struct discr_tree::edge_cmp {
    int operator()(edge const & e1, edge const & e2) const {
        if (e1.m_fn != e2.m_fn)
           return static_cast<int>(e1.m_fn) - static_cast<int>(e2.m_fn);
        if (e1.m_kind != e2.m_kind)
            return static_cast<int>(e1.m_kind) - static_cast<int>(e2.m_kind);
        return quick_cmp(e1.m_name, e2.m_name);
    }
};

struct discr_tree::node_cell {
    MK_LEAN_RC();
    /* Unique id. We use it to implement node_cmp */
    unsigned                      m_id;
    /* We use a map based tree to map edges to nodes, we should investigate whether we really need a tree here.
       We suspect the set of edges is usually quite small. So, an assoc-list may be enough.
       We should also investigate whether a small array + hash code based on the edge is not enough.
       Note that we may even ignore collisions since this is an imperfect discrimination tree anyway. */
    rb_map<edge, node, edge_cmp>  m_children;
    node                          m_star_child;
    /* The skip set is needed when searching for the set of terms stored in the discrimination tree
       that may match an input term containing metavariables. In the literature, they are called
       skip set/list. */
    rb_tree<node, node_cmp>       m_skip;
    rb_expr_tree                  m_values;
    void dealloc();
    node_cell();
    node_cell(node_cell const & s);
};

DEF_THREAD_MEMORY_POOL(get_allocator, sizeof(discr_tree::node_cell));
LEAN_THREAD_VALUE(unsigned, g_next_id, 0);
MK_THREAD_LOCAL_GET_DEF(std::vector<unsigned>, get_recycled_ids);

static unsigned mk_id() {
    auto & ids = get_recycled_ids();
    unsigned r;
    if (ids.empty()) {
        r = g_next_id;
        g_next_id++;
    } else {
        r = ids.back();
        ids.pop_back();
    }
    return r;
}

discr_tree::node_cell::node_cell():m_rc(0), m_id(mk_id()) {
}

discr_tree::node_cell::node_cell(node_cell const & s):
    m_rc(0), m_id(mk_id()),
    m_children(s.m_children),
    m_star_child(s.m_star_child),
    m_values(s.m_values) {
}

void discr_tree::node_cell::dealloc() {
    this->~node_cell();
    get_recycled_ids().push_back(m_id);
    get_allocator().recycle(this);
}

auto discr_tree::ensure_unshared(node && n) -> node {
    if (!n.m_ptr)
        return node(new (get_allocator().allocate()) node_cell());
    else if (n.is_shared())
        return node(new (get_allocator().allocate()) node_cell(*n.m_ptr));
    else
        return n;
}

discr_tree::node::node(node_cell * ptr):m_ptr(ptr) { if (m_ptr) ptr->inc_ref(); }
discr_tree::node::node(node const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
discr_tree::node::node(node && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
discr_tree::node::~node() { if (m_ptr) m_ptr->dec_ref(); }

discr_tree::node & discr_tree::node::operator=(node const & n) { LEAN_COPY_REF(n); }
discr_tree::node & discr_tree::node::operator=(node&& n) { LEAN_MOVE_REF(n); }
bool discr_tree::node::is_shared() const { return m_ptr && m_ptr->get_rc() > 1; }

int discr_tree::node_cmp::operator()(node const & n1, node const & n2) const {
    if (n1.m_ptr) {
        return n2.m_ptr ? unsigned_cmp()(n1.m_ptr->m_id, n2.m_ptr->m_id) : 1;
    } else {
        return n2.m_ptr ? -1 : 0;
    }
}

auto discr_tree::insert_erase_atom(type_context_old & ctx, node && n, edge const & e, buffer<pair<expr, bool>> & todo,
                                   expr const & v, buffer<pair<node, node>> & skip, bool ins) -> node {
    node new_n = ensure_unshared(n.steal());
    if (auto child = new_n.m_ptr->m_children.find(e)) {
        node new_child(*child);
        new_n.m_ptr->m_children.erase(e);
        new_child = insert_erase(ctx, new_child.steal(), false, todo, v, skip, ins);
        new_n.m_ptr->m_children.insert(e, new_child);
        return new_n;
    } else {
        node new_child = insert_erase(ctx, node(), false, todo, v, skip, ins);
        new_n.m_ptr->m_children.insert(e, new_child);
        return new_n;
    }
}

auto discr_tree::insert_erase_star(type_context_old & ctx, node && n, buffer<pair<expr, bool>> & todo, expr const & v,
                                   buffer<pair<node, node>> & skip, bool ins) -> node {
    node new_n = ensure_unshared(n.steal());
    new_n.m_ptr->m_star_child = insert_erase(ctx, new_n.m_ptr->m_star_child.steal(), false, todo, v, skip, ins);
    return new_n;
}

auto discr_tree::insert_erase_app(type_context_old & ctx,
                                  node && n, bool is_root, expr const & e, buffer<pair<expr, bool>> & todo, expr const & v,
                                  buffer<pair<node, node>> & skip, bool ins) -> node {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn) || is_local(fn)) {
        if (!is_root)
            todo.push_back(mk_pair(*g_delimiter, false));
        fun_info info = get_fun_info(ctx, fn, args.size());
        buffer<param_info> pinfos;
        to_buffer(info.get_params_info(), pinfos);
        lean_assert(pinfos.size() == args.size());
        unsigned i = args.size();
        while (i > 0) {
            --i;
            if (pinfos[i].is_prop() || pinfos[i].is_inst_implicit() || pinfos[i].is_implicit())
                continue; // We ignore propositions, implicit and inst-implict arguments
            todo.push_back(mk_pair(args[i], false));
        }
        todo.push_back(mk_pair(fn, true));
        node new_n = insert_erase(ctx, std::move(n), false, todo, v, skip, ins);
        if (!is_root) {
            lean_assert(!skip.empty());
            // Update skip set.
            pair<node, node> const & p = skip.back();
            new_n.m_ptr->m_skip.erase(p.first);   // remove old skip node
            new_n.m_ptr->m_skip.insert(p.second); // insert new skip node
            skip.pop_back();
        }
        return new_n;
    } else if (is_meta(fn)) {
        return insert_erase_star(ctx, std::move(n), todo, v, skip, ins);
    } else {
        return insert_erase_atom(ctx, std::move(n), edge(edge_kind::Unsupported), todo, v, skip, ins);
    }
}

auto discr_tree::insert_erase(type_context_old & ctx,
                              node && n, bool is_root, buffer<pair<expr, bool>> & todo,
                              expr const & v, buffer<pair<node, node>> & skip, bool ins) -> node {
    if (todo.empty()) {
        node new_n = ensure_unshared(n.steal());
        if (ins)
            new_n.m_ptr->m_values.insert(v);
        else
            new_n.m_ptr->m_values.erase(v);
        return new_n;
    }

    pair<expr, bool> p = todo.back();
    todo.pop_back();
    expr const & e = p.first;
    bool fn        = p.second;

    if (is_eqp(e, *g_delimiter)) {
        node old_n(n);
        node new_n = insert_erase(ctx, std::move(n), false, todo, v, skip, ins);
        skip.emplace_back(old_n, new_n);
        return new_n;
    }

    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Local:
        return insert_erase_atom(ctx, std::move(n), edge(e, fn), todo, v, skip, ins);
    case expr_kind::Meta:
        return insert_erase_star(ctx, std::move(n), todo, v, skip, ins);
    case expr_kind::App:
        return insert_erase_app(ctx, std::move(n), is_root, e, todo, v, skip, ins);
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Sort: case expr_kind::Lambda:
    case expr_kind::Pi:   case expr_kind::Macro:
    case expr_kind::Let:
        // unsupported
        return insert_erase_atom(ctx, std::move(n), edge(edge_kind::Unsupported), todo, v, skip, ins);
    }
    lean_unreachable();
}

void discr_tree::insert_erase(type_context_old & ctx, expr const & k, expr const & v, bool ins) {
    // insert & erase operations.
    // The erase operation is not optimal because it does not eliminate dead branches from the tree.
    // If this becomes an issue, we can remove dead branches from time to time and/or reconstruct
    // the tree from time to time.
    buffer<pair<expr, bool>> todo;
    buffer<pair<node, node>> skip;
    todo.push_back(mk_pair(k, false));
    m_root = insert_erase(ctx, m_root.steal(), true, todo, v, skip, ins);
    lean_trace("discr_tree", tout() << "\n"; trace(););
}

bool discr_tree::find_atom(type_context_old & ctx, node const & n, edge const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    if (auto child = n.m_ptr->m_children.find(e)) {
        return find(ctx, *child, todo, fn);
    } else {
        return true; // continue
    }
}

bool discr_tree::find_star(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    bool cont = true;
    n.m_ptr->m_skip.for_each([&](node const & skip_child) {
            if (cont && !find(ctx, skip_child, todo, fn))
                cont = false;
        });
    if (!cont)
        return false;
    // we also have to traverse children whose edge is an atom.
    n.m_ptr->m_children.for_each([&](edge const & e, node const & child) {
            if (cont && !e.m_fn && !find(ctx, child, todo, fn))
                cont = false;
        });
    return cont;
}

bool discr_tree::find_app(type_context_old & ctx, node const & n, expr const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (is_constant(f) || is_local(f)) {
        fun_info info = get_fun_info(ctx, f, args.size());
        buffer<param_info> pinfos;
        to_buffer(info.get_params_info(), pinfos);
        lean_assert(pinfos.size() == args.size());
        unsigned i = args.size();
        list<pair<expr, bool>> new_todo = todo;
        while (i > 0) {
            --i;
            if (pinfos[i].is_prop() || pinfos[i].is_inst_implicit() || pinfos[i].is_implicit())
                continue; // We ignore propositions, implicit and inst-implict arguments
            new_todo = cons(mk_pair(args[i], false), new_todo);
        }
        new_todo = cons(mk_pair(f, true), new_todo);
        return find(ctx, n, new_todo, fn);
    } else if (is_meta(f)) {
        return find_star(ctx, n, todo, fn);
    } else {
        return find_atom(ctx, n, edge(edge_kind::Unsupported), todo, fn);
    }
}

bool discr_tree::find(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    if (!todo) {
        bool cont = true;
        n.m_ptr->m_values.for_each([&](expr const & v) {
                if (cont && !fn(v))
                    cont = false;
            });
        return cont;
    }

    if (n.m_ptr->m_star_child && !find(ctx, n.m_ptr->m_star_child, tail(todo), fn))
        return false; // stop search

    pair<expr, bool> const & p = head(todo);
    expr const & e = p.first;
    bool is_fn     = p.second;

    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Local:
        return find_atom(ctx, n, edge(e, is_fn), tail(todo), fn);
    case expr_kind::Meta:
        return find_star(ctx, n, tail(todo), fn);
    case expr_kind::App:
        return find_app(ctx, n, e, tail(todo), fn);
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Sort: case expr_kind::Lambda:
    case expr_kind::Pi:   case expr_kind::Macro:
    case expr_kind::Let:
        // unsupported
        return find_atom(ctx, n, edge(edge_kind::Unsupported), tail(todo), fn);
    }
    lean_unreachable();
}

void discr_tree::find(type_context_old & ctx, expr const & e, std::function<bool(expr const &)> const & fn) const { // NOLINT
    if (m_root)
        find(ctx, m_root, to_list(mk_pair(e, false)), fn);
}

void discr_tree::collect(type_context_old & ctx, expr const & e, buffer<expr> & r) const {
    find(ctx, e, [&](expr const & v) { r.push_back(v); return true; });
}

static void indent(unsigned depth) {
    for (unsigned i = 0; i < depth; i++) tout() << "  ";
}

void discr_tree::node::trace(optional<edge> const & e, unsigned depth, bool disj) const {
    if (!m_ptr) {
        tout() << "[null]\n";
        return;
    }
    indent(depth);
    if (disj)
        tout() << "| ";
    else if (depth > 0)
        tout() << "  ";
    if (e) {
        switch (e->m_kind) {
        case edge_kind::Constant:
            tout() << e->m_name;
            break;
        case edge_kind::Local:
            tout() << e->m_name;
            break;
        case edge_kind::Star:
            tout() << "*";
            break;
        case edge_kind::Unsupported:
            tout() << "#";
            break;
        }
        if (e->m_fn)
            tout() << " (fn)";
        tout() << " -> ";
    }
    tout() << "[" << m_ptr->m_id << "] {";
    bool first = true;
    m_ptr->m_skip.for_each([&](node const & s) {
            if (first) first = false; else tout() << ", ";
            tout() << s.m_ptr->m_id;
        });
    tout() << "}";
    if (!m_ptr->m_values.empty()) {
        tout() << " {";
        first = true;
        m_ptr->m_values.for_each([&](expr const & v) {
                if (first) first = false; else tout() << ", ";
                tout() << v;
            });
        tout() << "}";
    }
    tout() << "\n";
    unsigned new_depth = depth;
    unsigned num_children = m_ptr->m_children.size();
    if (m_ptr->m_star_child)
        num_children++;
    if (num_children > 1)
        new_depth++;
    m_ptr->m_children.for_each([&](edge const & e, node const & n) {
            n.trace(optional<edge>(e), new_depth, num_children > 1);
        });
    if (m_ptr->m_star_child) {
        m_ptr->m_star_child.trace(optional<edge>(edge_kind::Star), new_depth, num_children > 1);
    }
}

void discr_tree::trace() const {
    m_root.trace(optional<edge>(), 0, false);
}

void initialize_discr_tree() {
    register_trace_class(name{"discr_tree"});
    g_delimiter = new expr(mk_constant(name::mk_internal_unique_name()));
}

void finalize_discr_tree() {
    delete g_delimiter;
}
}
