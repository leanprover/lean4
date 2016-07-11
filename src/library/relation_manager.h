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

/** \brief If \c rop is a registered relation, then return a non-null pointer to the associated information
    Lean assumes that the arguments of the binary relation are the last two explicit arguments.
    Everything else is assumed to be a parameter.
*/
relation_info const * get_relation_info(environment const & env, name const & rop);
inline bool is_relation(environment const & env, name const & rop) { return get_relation_info(env, rop) != nullptr; }

typedef std::function<optional<relation_info>(name const &)>  relation_info_getter;
relation_info_getter mk_relation_info_getter(environment const & env);

/** \brief Return true iff \c e is of the form (lhs rop rhs) where rop is a registered relation. */
bool is_relation(environment const & env, expr const & e, name & rop, expr & lhs, expr & rhs);
typedef std::function<bool(expr const &, name &, expr &, expr &)> is_relation_pred; // NOLINT
/** \brief Construct an \c is_relation predicate for the given environment. */
is_relation_pred mk_is_relation_pred(environment const & env);

/** \brief Declare a new binary relation named \c n */
environment add_relation(environment const & env, name const & n, bool persistent);

/** \brief Declare subst/refl/symm/trans lemmas for a binary relation,
 * it also declares the relation if it has not been declared yet */
environment add_subst(environment const & env, name const & n, bool persistent);
environment add_refl(environment const & env, name const & n, bool persistent);
environment add_symm(environment const & env, name const & n, bool persistent);
environment add_trans(environment const & env, name const & n, bool persistent);

struct relation_lemma_info {
    name     m_name;
    unsigned m_num_univs;
    unsigned m_num_args;
    relation_lemma_info() {}
    relation_lemma_info(name const & n, unsigned nunivs, unsigned nargs):m_name(n), m_num_univs(nunivs), m_num_args(nargs) {}
};

typedef relation_lemma_info refl_info;
typedef relation_lemma_info symm_info;
typedef relation_lemma_info subst_info;

struct trans_info : public relation_lemma_info {
    name  m_res_relation;
    trans_info() {}
    trans_info(name const & n, unsigned nunivs, unsigned nargs, name const & rel):
        relation_lemma_info(n, nunivs, nargs), m_res_relation(rel) {}
};

optional<subst_info> get_subst_extra_info(environment const & env, name const & op);
optional<refl_info> get_refl_extra_info(environment const & env, name const & op);
optional<symm_info> get_symm_extra_info(environment const & env, name const & op);
optional<trans_info> get_trans_extra_info(environment const & env, name const & op1, name const & op2);
optional<name> get_refl_info(environment const & env, name const & op);
optional<name> get_symm_info(environment const & env, name const & op);
optional<name> get_trans_info(environment const & env, name const & op);

typedef std::function<optional<refl_info>(name const &)>  refl_info_getter;
typedef std::function<optional<trans_info>(name const &, name const &)> trans_info_getter;
typedef std::function<optional<symm_info>(name const &)>  symm_info_getter;

refl_info_getter mk_refl_info_getter(environment const & env);
trans_info_getter mk_trans_info_getter(environment const & env);
symm_info_getter mk_symm_info_getter(environment const & env);

bool is_subst_relation(environment const & env, name const & op);
inline bool is_trans_relation(environment const & env, name const & op) { return static_cast<bool>(get_trans_info(env, op)); }
inline bool is_symm_relation(environment const & env, name const & op) { return static_cast<bool>(get_symm_info(env, op)); }
inline bool is_refl_relation(environment const & env, name const & op) { return static_cast<bool>(get_refl_info(env, op)); }

void initialize_relation_manager();
void finalize_relation_manager();
}
