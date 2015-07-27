/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"
#include "library/head_map.h"
#include "library/io_state_stream.h"

namespace lean {
class simp_rule_sets;

class simp_rule_core {
protected:
    name           m_id;
    levels         m_univ_metas;
    list<expr>     m_metas;
    expr           m_lhs;
    expr           m_rhs;
    expr           m_proof;
    simp_rule_core(name const & id, levels const & univ_metas, list<expr> const & metas,
                   expr const & lhs, expr const & rhs, expr const & proof);
public:
    name const & get_id() const { return m_id; }
    levels const & get_univ_metas() const { return m_univ_metas; }
    list<expr> const & get_metas() const { return m_metas; }
    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
    expr const & get_proof() const { return m_proof; }
};

class simp_rule : public simp_rule_core {
    bool           m_is_permutation;
    simp_rule(name const & id, levels const & univ_metas, list<expr> const & metas,
              expr const & lhs, expr const & rhs, expr const & proof, bool is_perm);
    friend simp_rule_sets add_core(type_checker & tc, simp_rule_sets const & s, name const & id,
                                   levels const & univ_metas, expr const & e, expr const & h);
public:
    friend bool operator==(simp_rule const & r1, simp_rule const & r2);
    bool is_perm() const { return m_is_permutation; }
    format pp(formatter const & fmt) const;
};

bool operator==(simp_rule const & r1, simp_rule const & r2);
inline bool operator!=(simp_rule const & r1, simp_rule const & r2) { return !operator==(r1, r2); }

class congr_rule : public simp_rule_core {
    list<expr>  m_congr_hyps;
    congr_rule(name const & id, levels const & univ_metas, list<expr> const & metas,
               expr const & lhs, expr const & rhs, expr const & proof, list<expr> const & congr_hyps);
    friend void add_congr_core(environment const & env, simp_rule_sets & s, name const & n);
public:
    friend bool operator==(congr_rule const & r1, congr_rule const & r2);
    list<expr> const & get_congr_hyps() const { return m_congr_hyps; }
    format pp(formatter const & fmt) const;
};

bool operator==(congr_rule const & r1, congr_rule const & r2);
inline bool operator!=(congr_rule const & r1, congr_rule const & r2) { return !operator==(r1, r2); }

class simp_rule_set {
    typedef head_map<simp_rule>  simp_set;
    typedef head_map<congr_rule> congr_set;
    name      m_eqv;
    simp_set  m_simp_set;
    congr_set m_congr_set;
public:
    simp_rule_set() {}
    /** \brief Return the equivalence relation associated with this set */
    simp_rule_set(name const & eqv);
    bool empty() const { return m_simp_set.empty() && m_congr_set.empty(); }
    name const & get_eqv() const { return m_eqv; }
    void insert(simp_rule const & r);
    void erase(simp_rule const & r);
    void insert(congr_rule const & r);
    void erase(congr_rule const & r);
    void erase_simp(name_set const & ids);
    void erase_simp(buffer<name> const & ids);
    list<simp_rule> const * find_simp(head_index const & h) const;
    void for_each_simp(std::function<void(simp_rule const &)> const & fn) const;
    list<congr_rule> const * find_congr(head_index const & h) const;
    void for_each_congr(std::function<void(congr_rule const &)> const & fn) const;
};

class simp_rule_sets {
    name_map<simp_rule_set> m_sets; // mapping from relation name to simp_rule_set
    template<typename R> void insert_core(name const & eqv, R const & r);
    template<typename R> void erase_core(name const & eqv, R const & r);
public:
    void insert(name const & eqv, simp_rule const & r);
    void erase(name const & eqv, simp_rule const & r);
    void insert(name const & eqv, congr_rule const & r);
    void erase(name const & eqv, congr_rule const & r);
    void erase_simp(name_set const & ids);
    void erase_simp(buffer<name> const & ids);
    void get_relations(buffer<name> & rs) const;
    simp_rule_set const * find(name const & eqv) const;
    list<simp_rule> const * find_simp(name const & eqv, head_index const & h) const;
    list<congr_rule> const * find_congr(name const & eqv, head_index const & h) const;
    void for_each_simp(std::function<void(name const &, simp_rule const &)> const & fn) const;
    void for_each_congr(std::function<void(name const &, congr_rule const &)> const & fn) const;
    format pp(formatter const & fmt, format const & header, bool simp, bool congr) const;
    format pp_simp(formatter const & fmt, format const & header) const;
    format pp_simp(formatter const & fmt) const;
    format pp_congr(formatter const & fmt) const;
    format pp(formatter const & fmt) const;
};

simp_rule_sets add(type_checker & tc, simp_rule_sets const & s, name const & id, expr const & e, expr const & h);
simp_rule_sets join(simp_rule_sets const & s1, simp_rule_sets const & s2);

environment add_simp_rule(environment const & env, name const & n, bool persistent = true);
environment add_congr_rule(environment const & env, name const & n, bool persistent = true);

/** \brief Return true if \c n is an active simplification rule in \c env */
bool is_simp_rule(environment const & env, name const & n);
/** \brief Return true if \c n is an active congruence rule in \c env */
bool is_congr_rule(environment const & env, name const & n);
/** \brief Get current simplification rule sets */
simp_rule_sets get_simp_rule_sets(environment const & env);
/** \brief Get simplification rule sets in the given namespace. */
simp_rule_sets get_simp_rule_sets(environment const & env, name const & ns);

io_state_stream const & operator<<(io_state_stream const & out, simp_rule_sets const & s);

void initialize_simp_rule_set();
void finalize_simp_rule_set();
}
