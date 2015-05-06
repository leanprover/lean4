/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class obtain_struct {
    bool                m_leaf;
    list<obtain_struct> m_children;
public:
    obtain_struct():m_leaf(true) {}
    obtain_struct(list<obtain_struct> const & c):m_leaf(false), m_children(c) {}
    bool is_leaf() const { return m_leaf; }
    list<obtain_struct> const & get_children() const { return m_children; }
    void write(serializer & s) const;
    unsigned size() const;
};

expr mk_obtain_expr(obtain_struct const & s, buffer<expr> const & decls, expr const & from, expr const & goal);
bool is_obtain_expr(expr const & e);
void decompose_obtain(expr const & e, obtain_struct & s, expr & from, expr & decls_goal);
void initialize_obtain_expr();
void finalize_obtain_expr();
}
