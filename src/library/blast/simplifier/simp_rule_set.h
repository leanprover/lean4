/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tmp_type_context.h"
#include "library/head_map.h"
#include "library/io_state_stream.h"

#ifndef LEAN_SIMP_DEFAULT_PRIORITY
#define LEAN_SIMP_DEFAULT_PRIORITY 1000
#endif

namespace lean {
class simp_rule_sets;

class simp_rule_core {
protected:
    name                m_id;
    levels              m_umetas;
    list<expr>          m_emetas;
    list<bool>          m_instances;

    expr                m_lhs;
    expr                m_rhs;
    expr                m_proof;
    unsigned            m_priority;
    simp_rule_core(name const & id, levels const & umetas, list<expr> const & emetas,
                   list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
                   unsigned priority);
public:
    name const & get_id() const { return m_id; }
    unsigned get_num_umeta() const { return length(m_umetas); }
    unsigned get_num_emeta() const { return length(m_emetas); }

    /** \brief Return a list containing the expression metavariables in reverse order. */
    list<expr> const & get_emetas() const { return m_emetas; }

    /** \brief Return a list of bools indicating whether or not each expression metavariable
        in <tt>get_emetas()</tt> is an instance. */
    list<bool> const & get_instances() const { return m_instances; }

    unsigned get_priority() const { return m_priority; }

    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
    expr const & get_proof() const { return m_proof; }
};

class simp_rule : public simp_rule_core {
    bool           m_is_permutation;
    simp_rule(name const & id, levels const & umetas, list<expr> const & emetas,
              list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
              bool is_perm, unsigned priority);

    friend simp_rule_sets add_core(tmp_type_context & tctx, simp_rule_sets const & s, name const & id,
                                   levels const & univ_metas, expr const & e, expr const & h, unsigned priority);
public:
    friend bool operator==(simp_rule const & r1, simp_rule const & r2);
    bool is_perm() const { return m_is_permutation; }
    format pp(formatter const & fmt) const;
};

bool operator==(simp_rule const & r1, simp_rule const & r2);
inline bool operator!=(simp_rule const & r1, simp_rule const & r2) { return !operator==(r1, r2); }

class congr_rule : public simp_rule_core {
    list<expr>  m_congr_hyps;
    congr_rule(name const & id, levels const & umetas, list<expr> const & emetas,
               list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
               list<expr> const & congr_hyps, unsigned priority);
    friend void add_congr_core(tmp_type_context & tctx, simp_rule_sets & s, name const & n, unsigned priority);
public:
    friend bool operator==(congr_rule const & r1, congr_rule const & r2);
    list<expr> const & get_congr_hyps() const { return m_congr_hyps; }
    format pp(formatter const & fmt) const;
};

struct simp_rule_core_prio_fn { unsigned operator()(simp_rule_core const & s) const { return s.get_priority(); } };

bool operator==(congr_rule const & r1, congr_rule const & r2);
inline bool operator!=(congr_rule const & r1, congr_rule const & r2) { return !operator==(r1, r2); }

class simp_rule_set {
    typedef head_map_prio<simp_rule, simp_rule_core_prio_fn>  simp_set;
    typedef head_map_prio<congr_rule, simp_rule_core_prio_fn> congr_set;
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

simp_rule_sets add(tmp_type_context & tctx, simp_rule_sets const & s, name const & id, expr const & e, expr const & h, unsigned priority);
simp_rule_sets join(simp_rule_sets const & s1, simp_rule_sets const & s2);

environment add_simp_rule(environment const & env, name const & n, unsigned priority,  bool persistent);
environment add_congr_rule(environment const & env, name const & n, unsigned priority, bool persistent);

/** \brief Return true if \c n is an active simplification rule in \c env */
bool is_simp_rule(environment const & env, name const & n);
/** \brief Return true if \c n is an active congruence rule in \c env */
bool is_congr_rule(environment const & env, name const & n);
/** \brief Get current simplification rule sets */
simp_rule_sets get_simp_rule_sets(environment const & env);
/** \brief Get simplification rule sets in the given namespace. */
simp_rule_sets get_simp_rule_sets(environment const & env, io_state const & ios, name const & ns);
/** \brief Get simplification rule sets in the given namespaces. */
simp_rule_sets get_simp_rule_sets(environment const & env, io_state const & ios, std::initializer_list<name> const & nss);

io_state_stream const & operator<<(io_state_stream const & out, simp_rule_sets const & s);

void initialize_simplifier_rule_set();
void finalize_simplifier_rule_set();
}
