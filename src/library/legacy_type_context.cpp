/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/legacy_type_context.h"
#include "library/reducible.h"

namespace lean {
static name * g_tmp_prefix                   = nullptr;
legacy_type_context::legacy_type_context(environment const & env, options const & o,
                                         list<expr> const & insts, bool multiple_instances):
    type_context(env, o, multiple_instances),
    m_not_reducible_pred(mk_not_reducible_pred(env)) {
    m_ignore_if_zero = false;
    m_next_uvar_idx  = 0;
    m_next_mvar_idx  = 0;
    set_local_instances(insts);
}

legacy_type_context::~legacy_type_context() {}

bool legacy_type_context::is_uvar(level const & l) const {
    if (!is_meta(l))
        return false;
    name const & n = meta_id(l);
    return !n.is_atomic() && n.get_prefix() == *g_tmp_prefix;
}

bool legacy_type_context::is_mvar(expr const & e) const {
    if (!is_metavar(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.get_prefix() == *g_tmp_prefix;
}

unsigned legacy_type_context::uvar_idx(level const & l) const {
    lean_assert(is_uvar(l));
    return meta_id(l).get_numeral();
}

unsigned legacy_type_context::mvar_idx(expr const & m) const {
    lean_assert(is_mvar(m));
    return mlocal_name(m).get_numeral();
}

optional<level> legacy_type_context::get_assignment(level const & u) const {
    if (auto v = m_assignment.m_uassignment.find(uvar_idx(u)))
        return some_level(*v);
    else
        return none_level();
}

optional<expr> legacy_type_context::get_assignment(expr const & m) const {
    if (auto v = m_assignment.m_eassignment.find(mvar_idx(m)))
        return some_expr(*v);
    else
        return none_expr();
}

void legacy_type_context::update_assignment(level const & u, level const & v) {
    m_assignment.m_uassignment.insert(uvar_idx(u), v);
}

void legacy_type_context::update_assignment(expr const & m, expr const & v) {
    m_assignment.m_eassignment.insert(mvar_idx(m), v);
}

level legacy_type_context::mk_uvar() {
    unsigned idx = m_next_uvar_idx;
    m_next_uvar_idx++;
    return mk_meta_univ(name(*g_tmp_prefix, idx));
}

expr legacy_type_context::mk_mvar(expr const & type) {
    unsigned idx = m_next_mvar_idx;
    m_next_mvar_idx++;
    return mk_metavar(name(*g_tmp_prefix, idx), type);
}

optional<expr> legacy_type_context::mk_subsingleton_instance(expr const & type) {
    flet<bool> set(m_ignore_if_zero, true);
    return type_context::mk_subsingleton_instance(type);
}

bool legacy_type_context::ignore_universe_def_eq(level const & l1, level const & l2) const {
    if (is_meta(l1) || is_meta(l2)) {
        // The unifier may invoke this module before universe metavariables in the class
        // have been instantiated. So, we just ignore and assume they will be solved by
        // the unifier.

        // See comment at m_ignore_if_zero declaration.
        if (m_ignore_if_zero && (is_zero(l1) || is_zero(l2)))
            return false;
        return true; // we ignore
    } else {
        return false;
    }
}

bool legacy_type_context::validate_assignment_types(expr const &, expr const &) {
    // We disable this check because the interface between type_context and the elaborator unifier
    // is currently quite brittle.
    // Recall that this class is used to implement the type class inference in the Lean frontend.
    return true;
}

void initialize_legacy_type_context() {
    g_tmp_prefix      = new name(name::mk_internal_unique_name());
}

void finalize_legacy_type_context() {
    delete g_tmp_prefix;
}
}
