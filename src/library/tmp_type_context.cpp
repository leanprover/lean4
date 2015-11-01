/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tmp_type_context.h"
#include "library/idx_metavar.h"

namespace lean {
static name * g_prefix = nullptr;

tmp_type_context::tmp_type_context(environment const & env, io_state const & ios, reducible_behavior b):
    type_context(env, ios) {
    switch (b) {
    case UnfoldReducible:      m_opaque_pred = mk_not_reducible_pred(env);      break;
    case UnfoldQuasireducible: m_opaque_pred = mk_not_quasireducible_pred(env); break;
    case UnfoldSemireducible:  m_opaque_pred = mk_irreducible_pred(env);        break;
    }
    m_next_local_idx = 0;
}

tmp_type_context::~tmp_type_context() {
}

void tmp_type_context::clear() {
    m_next_local_idx = 0;
    m_uassignment.clear();
    m_eassignment.clear();
    m_trail.clear();
    m_scopes.clear();
}

void tmp_type_context::set_next_uvar_idx(unsigned next_idx) {
    lean_assert(m_uassignment.empty());
    lean_assert(m_scopes.empty());
    m_uassignment.resize(next_idx);
}

void tmp_type_context::set_next_mvar_idx(unsigned next_idx) {
    lean_assert(m_eassignment.empty());
    lean_assert(m_scopes.empty());
    m_eassignment.resize(next_idx);
}

expr tmp_type_context::mk_tmp_local(expr const & type, binder_info const & bi) {
    unsigned idx = m_next_local_idx;
    m_next_local_idx++;
    name n(*g_prefix, idx);
    return lean::mk_local(n, n, type, bi);
}

bool tmp_type_context::is_tmp_local(expr const & e) const {
    if (!is_local(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.get_prefix() == *g_prefix;
}

bool tmp_type_context::is_uvar(level const & l) const {
    return is_idx_metauniv(l);
}

bool tmp_type_context::is_mvar(expr const & e) const {
    return is_idx_metavar(e);
}

optional<level> tmp_type_context::get_assignment(level const & u) const {
    unsigned idx = to_meta_idx(u);
    // if the following assetion is violated, we have two options:
    // 1- We should create the meta-variable using mk_uvar
    // 2- We create using mk_idx_metauniv, and notify this object using
    //    set_next_uvar_idx
    lean_assert(idx < m_uassignment.size());
    return m_uassignment[idx];
}

optional<expr> tmp_type_context::get_assignment(expr const & m) const {
    unsigned idx = to_meta_idx(m);
    // if the following assetion is violated, we have two options:
    // 1- We should create the meta-variable using mk_mvar
    // 2- We create using mk_idx_metavar, and notify this object using
    //    set_next_mvar_idx
    lean_assert(idx < m_eassignment.size());
    return m_eassignment[idx];
}

void tmp_type_context::update_assignment(level const & u, level const & v) {
    unsigned idx = to_meta_idx(u);
    lean_assert(idx < m_uassignment.size()); // see comments above
    lean_assert(!m_uassignment[idx]);
    m_uassignment[idx] = v;
    if (!m_scopes.empty())
        m_trail.emplace_back(trail_kind::Level, idx);
}

void tmp_type_context::update_assignment(expr const & m, expr const & v) {
    unsigned idx = to_meta_idx(m);
    lean_assert(idx < m_eassignment.size()); // see comments above
    // Remark: type class resolution may update an already assigned meta-variable with a
    // definitionally equal, but the new assignment is "nicer", i.e., it has not been
    // accidentally unfolded by the unifier.
    // We only add the entry to the trail if it was not assigned before.
    bool was_assigned  = static_cast<bool>(m_eassignment[idx]);
    m_eassignment[idx] = v;
    if (!m_scopes.empty() && !was_assigned)
        m_trail.emplace_back(trail_kind::Expr, idx);
}

level tmp_type_context::mk_uvar() {
    unsigned idx = m_uassignment.size();
    m_uassignment.push_back(none_level());
    return mk_idx_metauniv(idx);
}

expr tmp_type_context::mk_mvar(expr const & type) {
    unsigned idx = m_eassignment.size();
    m_eassignment.push_back(none_expr());
    return mk_idx_metavar(idx, type);
}

void tmp_type_context::push() {
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_old_next_local_idx = m_next_local_idx;
    s.m_uassignment_sz     = m_uassignment.size();
    s.m_eassignment_sz     = m_eassignment.size();
    s.m_trail_sz           = m_trail.size();
}

void tmp_type_context::pop() {
    lean_assert(!m_scopes.empty());
    scope const & s  = m_scopes.back();
    m_next_local_idx = s.m_old_next_local_idx;
    unsigned old_sz  = s.m_trail_sz;
    unsigned i = m_trail.size();
    while (i > old_sz) {
        --i;
        pair<trail_kind, unsigned> const & p = m_trail.back();
        switch (p.first) {
        case trail_kind::Level: m_uassignment[p.second] = none_level(); break;
        case trail_kind::Expr:  m_eassignment[p.second] = none_expr();  break;
        }
        m_trail.pop_back();
    }
    lean_assert(m_trail.size() == old_sz);
    m_uassignment.resize(s.m_uassignment_sz);
    m_eassignment.resize(s.m_eassignment_sz);
}

void tmp_type_context::commit() {
    lean_assert(!m_scopes.empty());
    m_scopes.pop_back();
}
}
