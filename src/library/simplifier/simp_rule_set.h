/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"
#include "library/head_map.h"

namespace lean {
class simp_rule_sets;

class simp_rule {
    name           m_id;
    levels         m_univ_metas;
    list<expr>     m_metas;
    expr           m_lhs;
    expr           m_rhs;
    expr           m_proof;
    bool           m_is_permutation;
    simp_rule(name const & id, levels const & univ_metas, list<expr> const & metas,
              expr const & lhs, expr const & rhs, expr const & proof, bool is_perm);
    friend simp_rule_sets add_core(type_checker & tc, simp_rule_sets const & s, name const & id,
                                   levels const & univ_metas, expr const & e, expr const & h);
public:
    name const & get_id() const { return m_id; }
    levels const & get_univ_metas() const { return m_univ_metas; }
    list<expr> const & get_metas() const { return m_metas; }
    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
    expr const & get_proof() const { return m_proof; }
    bool is_perm() const { return m_is_permutation; }
    friend bool operator==(simp_rule const & r1, simp_rule const & r2);
    format pp(formatter const & fmt) const;
};

bool operator==(simp_rule const & r1, simp_rule const & r2);
inline bool operator!=(simp_rule const & r1, simp_rule const & r2) { return !operator==(r1, r2); }

class simp_rule_set {
    typedef head_map<simp_rule> rule_set;
    name     m_eqv;
    rule_set m_set;
public:
    simp_rule_set() {}
    /** \brief Return the equivalence relation associated with this set */
    simp_rule_set(name const & eqv);
    bool empty() const { return m_set.empty(); }
    name const & get_eqv() const { return m_eqv; }
    void insert(simp_rule const & r);
    void erase(simp_rule const & r);
    list<simp_rule> const * find(head_index const & h) const;
    void for_each(std::function<void(simp_rule const &)> const & fn) const;
};

class simp_rule_sets {
    name_map<simp_rule_set> m_sets; // mapping from relation name to simp_rule_set
public:
    void insert(name const & eqv, simp_rule const & r);
    void erase(name const & eqv, simp_rule const & r);
    void get_relations(buffer<name> & rs) const;
    simp_rule_set const * find(name const & eqv) const;
    list<simp_rule> const * find(name const & eqv, head_index const & h) const;
    void for_each(std::function<void(name const &, simp_rule const &)> const & fn) const;
};

simp_rule_sets add(type_checker & tc, simp_rule_sets const & s, name const & id, expr const & e, expr const & h);
simp_rule_sets join(simp_rule_sets const & s1, simp_rule_sets const & s2);

environment add_simp_rule(environment const & env, name const & n, bool persistent = true);
/** \brief Return true if \c n is an active rewrite rule in \c env */
bool is_simp_rule(environment const & env, name const & n);
/** \brief Get current rewrite rule sets */
simp_rule_sets get_simp_rule_sets(environment const & env);
/** \brief Get rewrite rule sets in the given namespace. */
simp_rule_sets get_simp_rule_set(environment const & env, name const & ns);
void initialize_simp_rule_set();
void finalize_simp_rule_set();
}
