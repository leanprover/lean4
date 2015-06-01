/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"
#include "library/head_map.h"

namespace lean {
class rewrite_rule_sets;

class rewrite_rule {
    name           m_id;
    list<expr>     m_metas;
    expr           m_lhs;
    expr           m_rhs;
    constraint_seq m_cs;
    expr           m_proof;
    bool           m_is_permutation;
    rewrite_rule(name const & id, list<expr> const & metas,
                 expr const & lhs, expr const & rhs, constraint_seq const & cs,
                 expr const & proof, bool is_perm);
    friend rewrite_rule_sets add(type_checker & tc, rewrite_rule_sets const & s, name const & id,
                                 expr const & e, expr const & h);
public:
    name const & get_id() const { return m_id; }
    list<expr> const & get_metas() const { return m_metas; }
    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
    constraint_seq const & get_cs() const { return m_cs; }
    expr const & get_proof() const { return m_proof; }
    bool is_perm() const { return m_is_permutation; }
    friend bool operator==(rewrite_rule const & r1, rewrite_rule const & r2);
};

bool operator==(rewrite_rule const & r1, rewrite_rule const & r2);
inline bool operator!=(rewrite_rule const & r1, rewrite_rule const & r2) { return !operator==(r1, r2); }

class rewrite_rule_set {
    typedef head_map<rewrite_rule> rule_set;
    name     m_eqv;
    rule_set m_set;
public:
    rewrite_rule_set() {}
    /** \brief Return the equivalence relation associated with this set */
    rewrite_rule_set(name const & eqv);
    bool empty() const { return m_set.empty(); }
    name const & get_eqv() const { return m_eqv; }
    void insert(rewrite_rule const & r);
    void erase(rewrite_rule const & r);
    list<rewrite_rule> const * find(head_index const & h) const;
    void for_each(std::function<void(rewrite_rule const &)> const & fn) const;
};

class rewrite_rule_sets {
    name_map<rewrite_rule_set> m_sets; // mapping from relation name to rewrite_rule_set
public:
    void insert(name const & eqv, rewrite_rule const & r);
    void erase(name const & eqv, rewrite_rule const & r);
    void get_relations(buffer<name> & rs) const;
    rewrite_rule_set const * find(name const & eqv) const;
    list<rewrite_rule> const * find(name const & eqv, head_index const & h) const;
    void for_each(std::function<void(name const &, rewrite_rule const &)> const & fn) const;
};

rewrite_rule_sets add(type_checker & tc, rewrite_rule_sets const & s, name const & id, expr const & e, expr const & h);
rewrite_rule_sets join(rewrite_rule_sets const & s1, rewrite_rule_sets const & s2);

environment add_rewrite_rule(environment const & env, name const & n, bool persistent = true);
/** \brief Get current rewrite rule sets */
rewrite_rule_sets get_rewrite_rule_sets(environment const & env);
/** \brief Get rewrite rule sets in the given namespace. */
rewrite_rule_sets get_rewrite_rule_set(environment const & env, name const & ns);
void initialize_rewrite_rule_set();
void finalize_rewrite_rule_set();
}
