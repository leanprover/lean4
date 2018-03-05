/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/type_context.h"

namespace lean {
/**
   \brief (Imperfect) discrimination trees.
   The edges are labeled with:
   1- Constant names (the universes are ignored)
   2- Local names (e.g., hypotheses)
   3- Star/Wildcard (we use them to encode metavariables). We use the same symbol
      for all metavariables. Remark: in the discrimination tree literature, our
      metavariables are called variables.
   4- Unsupported. We use them to encode nested lambda's, Pi's, Sort's
      Anything that is not an application, constant or local.
   When indexing terms, we ignore propositions and instance implicit
   arguments. We use get_fun_info procedure for retrieving
   this information. */
class discr_tree {
public:
    struct node_cell;
private:
    enum class edge_kind { Local, Constant, Star, Unsupported };
    struct edge;
    struct edge_cmp;
    struct node_cmp;
    struct node {
        node_cell * m_ptr;
        node():m_ptr(nullptr) {}
        node(node_cell * ptr);
        node(node const & s);
        node(node && s);

        ~node();
        node & operator=(node const & n);
        node & operator=(node&& n);
        operator bool() const { return m_ptr != nullptr; }
        bool is_shared() const;
        node steal() { node r; swap(r, *this); return r; }
        void trace(optional<edge> const & e, unsigned depth, bool disj) const;
    };
    static void swap(node & n1, node & n2);
    static node ensure_unshared(node && n);
    static node insert_erase_atom(type_context_old & ctx, node && n, edge const & e, buffer<pair<expr, bool>> & todo, expr const & v, buffer<pair<node, node>> & skip, bool ins);
    static node insert_erase_star(type_context_old & ctx, node && n, buffer<pair<expr, bool>> & todo, expr const & v, buffer<pair<node, node>> & skip, bool ins);
    static node insert_erase_app(type_context_old & ctx, node && n, bool is_root, expr const & e, buffer<pair<expr, bool>> & todo, expr const & v,
                                 buffer<pair<node, node>> & skip, bool ins);
    static node insert_erase(type_context_old & ctx, node && n, bool is_root, buffer<pair<expr, bool>> & todo,
                             expr const & v, buffer<pair<node, node>> & skip, bool ins);
    void insert_erase(type_context_old & ctx, expr const & k, expr const & v, bool ins);

    static bool find_atom(type_context_old & ctx, node const & n, edge const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT
    static bool find_star(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT
    static bool find_app(type_context_old & ctx, node const & n, expr const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT
    static bool find(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT

    node m_root;
public:
    void insert(type_context_old & ctx, expr const & k, expr const & v) { insert_erase(ctx, k, v, true); }
    void insert(type_context_old & ctx, expr const & k) { insert(ctx, k, k); }
    void erase(type_context_old & ctx, expr const & k, expr const & v) { insert_erase(ctx, k, v, false); }
    void erase(type_context_old & ctx, expr const & k) { erase(ctx, k, k); }

    void find(type_context_old & ctx, expr const & e, std::function<bool(expr const &)> const & fn) const; // NOLINT
    void collect(type_context_old & ctx, expr const & e, buffer<expr> & r) const;

    void trace() const;
};
void initialize_discr_tree();
void finalize_discr_tree();
}
