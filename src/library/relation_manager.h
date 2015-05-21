/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
struct relation_info {
    unsigned m_arity;
    unsigned m_lhs_pos;
    unsigned m_rhs_pos;
public:
    relation_info() {}
    relation_info(unsigned arity, unsigned lhs, unsigned rhs):
        m_arity(arity), m_lhs_pos(lhs), m_rhs_pos(rhs) {
        lean_assert(m_lhs_pos < m_arity);
        lean_assert(m_rhs_pos < m_arity);
    }
    unsigned get_arity() const { return m_arity; }
    unsigned get_lhs_pos() const { return m_lhs_pos; }
    unsigned get_rhs_pos() const { return m_rhs_pos; }
};

/** \brief Return true if \c rop is a registered equivalence relation in the given manager */
bool is_equivalence(environment const & env, name const & rop);

/** \brief If \c rop is a registered relation, then return a non-null pointer to the associated information */
relation_info const * get_relation_info(environment const & env, name const & rop);

environment add_subst(environment const & env, name const & n, bool persistent = true);
environment add_refl(environment const & env, name const & n, bool persistent = true);
environment add_symm(environment const & env, name const & n, bool persistent = true);
environment add_trans(environment const & env, name const & n, bool persistent = true);
optional<std::tuple<name, unsigned, unsigned>> get_refl_extra_info(environment const & env, name const & op);
optional<std::tuple<name, unsigned, unsigned>> get_subst_extra_info(environment const & env, name const & op);
optional<std::tuple<name, unsigned, unsigned>> get_symm_extra_info(environment const & env, name const & op);
optional<std::tuple<name, name, unsigned>> get_trans_extra_info(environment const & env, name const & op1, name const & op2);
optional<name> get_refl_info(environment const & env, name const & op);
optional<name> get_symm_info(environment const & env, name const & op);
optional<name> get_trans_info(environment const & env, name const & op);
void initialize_relation_manager();
void finalize_relation_manager();
}
