/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/flet.h"
#include "kernel/equiv_manager.h"

namespace lean {
auto equiv_manager::mk_node() -> node_ref {
    node_ref r = m_nodes.size();
    node n;
    n.m_parent = r;
    n.m_rank   = 0;
    m_nodes.push_back(n);
    return r;
}

auto equiv_manager::find(node_ref n) -> node_ref {
    while (true) {
        node_ref p = m_nodes[n].m_parent;
        if (p == n)
            return p;
        n = p;
    }
}

void equiv_manager::merge(node_ref n1, node_ref n2) {
    node_ref r1 = find(n1);
    node_ref r2 = find(n2);
    if (r1 != r2) {
        node & ref1 = m_nodes[r1];
        node & ref2 = m_nodes[r2];
        if (ref1.m_rank < ref2.m_rank) {
            ref1.m_parent = r2;
        } else if (ref1.m_rank > ref2.m_rank) {
            ref2.m_parent = r1;
        } else {
            ref2.m_parent = r1;
            ref1.m_rank++;
        }
    }
}

auto equiv_manager::to_node(expr const & e) -> node_ref {
    auto it = m_to_node.find(e);
    if (it != m_to_node.end())
        return it->second;
    node_ref r = mk_node();
    m_to_node.insert(mk_pair(e, r));
    return r;
}

bool equiv_manager::is_equiv_core(expr const & a, expr const & b) {
    if (is_eqp(a, b))                       return true;
    if (m_use_hash && a.hash() != b.hash()) return false;
    if (is_var(a) && is_var(b))             return var_idx(a) == var_idx(b);
    node_ref r1 = find(to_node(a));
    node_ref r2 = find(to_node(b));
    if (r1 == r2)
        return true;
    // fall back to structural equality
    if (a.kind() != b.kind())
        return false;
    check_system("expression equivalence test");
    bool result = false;
    switch (a.kind()) {
    case expr_kind::Var:
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::Constant:
        result =
            const_name(a) == const_name(b) &&
            compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        break;
    case expr_kind::Meta: case expr_kind::Local:
        result =
            mlocal_name(a) == mlocal_name(b) &&
            is_equiv_core(mlocal_type(a), mlocal_type(b));
        break;
    case expr_kind::App:
        result =
            is_equiv_core(app_fn(a), app_fn(b)) &&
            is_equiv_core(app_arg(a), app_arg(b));
        break;
    case expr_kind::Lambda: case expr_kind::Pi:
        result =
            is_equiv_core(binding_domain(a), binding_domain(b)) &&
            is_equiv_core(binding_body(a), binding_body(b));
        break;
    case expr_kind::Sort:
        result = sort_level(a) == sort_level(b);
        break;
    case expr_kind::Let:
        result =
            is_equiv_core(let_type(a), let_type(b)) &&
            is_equiv_core(let_value(a), let_value(b)) &&
            is_equiv_core(let_body(a), let_body(b));
        break;
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b) || macro_num_args(a) != macro_num_args(b))
            return false;
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (!is_equiv_core(macro_arg(a, i), macro_arg(b, i)))
                return false;
        }
        result = true;
        break;
    }
    if (result)
        merge(r1, r2);
    return result;
}

bool equiv_manager::is_equiv(expr const & a, expr const & b, bool use_hash) {
    flet<bool> set(m_use_hash, use_hash);
    return is_equiv_core(a, b);
}

void equiv_manager::add_equiv(expr const & e1, expr const & e2) {
    node_ref r1 = to_node(e1);
    node_ref r2 = to_node(e2);
    merge(r1, r2);
}
}
