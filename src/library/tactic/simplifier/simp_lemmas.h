/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/type_context.h"
#include "library/head_map.h"

namespace lean {

environment add_simp_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent);
environment add_congr_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent);
unsigned get_simp_lemma_priority(environment const & env, name const & n);

bool is_simp_lemma(environment const & env, name const & n);
bool is_congr_lemma(environment const & env, name const & n);
void get_simp_lemma_names(environment const & env, buffer<name> & r);
void get_congr_lemma_names(environment const & env, buffer<name> & r);

void initialize_simp_lemmas();
void finalize_simp_lemmas();

/** Generate a unique id for a set of namespaces containing [simp] and [congr] lemmas */
unsigned register_simp_lemmas(std::initializer_list<name> const & nss);

class simp_lemmas;
class simp_lemma_core {
protected:
    name                m_id;
    levels              m_umetas;
    list<expr>          m_emetas;
    list<bool>          m_instances;

    expr                m_lhs;
    expr                m_rhs;
    expr                m_proof;
    unsigned            m_priority;
    simp_lemma_core(name const & id, levels const & umetas, list<expr> const & emetas,
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

class simp_lemma : public simp_lemma_core {
    bool           m_is_permutation;
    simp_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
               list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
               bool is_perm, unsigned priority);

    friend simp_lemmas add_core(tmp_type_context & tmp_tctx, simp_lemmas const & s, name const & id,
                                levels const & univ_metas, expr const & e, expr const & h, unsigned priority);
public:
    friend bool operator==(simp_lemma const & r1, simp_lemma const & r2);
    bool is_perm() const { return m_is_permutation; }
    format pp(formatter const & fmt) const;
};

bool operator==(simp_lemma const & r1, simp_lemma const & r2);
inline bool operator!=(simp_lemma const & r1, simp_lemma const & r2) { return !operator==(r1, r2); }

// We use user_congr_lemma to avoid a confusion with ::lemma::congr_lemma
class user_congr_lemma : public simp_lemma_core {
    list<expr>  m_congr_hyps;
    user_congr_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                     list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
                     list<expr> const & congr_hyps, unsigned priority);
    friend simp_lemmas add_congr_core(tmp_type_context & tctx, simp_lemmas const & s, name const & n, unsigned priority);
public:
    friend bool operator==(user_congr_lemma const & r1, user_congr_lemma const & r2);
    list<expr> const & get_congr_hyps() const { return m_congr_hyps; }
    format pp(formatter const & fmt) const;
};

struct simp_lemma_core_prio_fn { unsigned operator()(simp_lemma_core const & s) const { return s.get_priority(); } };

bool operator==(user_congr_lemma const & r1, user_congr_lemma const & r2);
inline bool operator!=(user_congr_lemma const & r1, user_congr_lemma const & r2) { return !operator==(r1, r2); }

/** \brief Simplification and congruence lemmas for a given equivalence relation */
class simp_lemmas_for {
    typedef head_map_prio<simp_lemma, simp_lemma_core_prio_fn>  simp_set;
    typedef head_map_prio<user_congr_lemma, simp_lemma_core_prio_fn> congr_set;
    name      m_eqv;
    simp_set  m_simp_set;
    congr_set m_congr_set;
public:
    simp_lemmas_for() {}
    /** \brief Return the equivalence relation associated with this set */
    simp_lemmas_for(name const & eqv);
    bool empty() const { return m_simp_set.empty() && m_congr_set.empty(); }
    name const & get_eqv() const { return m_eqv; }
    void insert(simp_lemma const & r);
    void erase(simp_lemma const & r);
    void insert(user_congr_lemma const & r);
    void erase(user_congr_lemma const & r);
    void erase_simp(name_set const & ids);
    void erase_simp(buffer<name> const & ids);
    list<simp_lemma> const * find_simp(head_index const & h) const;
    void for_each_simp(std::function<void(simp_lemma const &)> const & fn) const;
    list<user_congr_lemma> const * find_congr(head_index const & h) const;
    void for_each_congr(std::function<void(user_congr_lemma const &)> const & fn) const;
};

class simp_lemmas {
    name_map<simp_lemmas_for> m_sets; // mapping from relation name to simp_lemmas_for
    template<typename R> void insert_core(name const & eqv, R const & r);
    template<typename R> void erase_core(name const & eqv, R const & r);
public:
    void insert(name const & eqv, simp_lemma const & r);
    void erase(name const & eqv, simp_lemma const & r);
    void insert(name const & eqv, user_congr_lemma const & r);
    void erase(name const & eqv, user_congr_lemma const & r);
    void erase_simp(name_set const & ids);
    void erase_simp(buffer<name> const & ids);
    void get_relations(buffer<name> & rs) const;
    simp_lemmas_for const * find(name const & eqv) const;
    list<simp_lemma> const * find_simp(name const & eqv, head_index const & h) const;
    list<user_congr_lemma> const * find_congr(name const & eqv, head_index const & h) const;
    void for_each_simp(std::function<void(name const &, simp_lemma const &)> const & fn) const;
    void for_each_congr(std::function<void(name const &, user_congr_lemma const &)> const & fn) const;
    format pp(formatter const & fmt, format const & header, bool simp, bool congr) const;
    format pp_simp(formatter const & fmt, format const & header) const;
    format pp_simp(formatter const & fmt) const;
    format pp_congr(formatter const & fmt) const;
    format pp(formatter const & fmt) const;
};

struct simp_lemmas_cache;

/** \brief Auxiliary class for initializing simp lemmas during blast initialization. */
class scope_simp {
    simp_lemmas_cache * m_old_cache;
public:
    scope_simp();
    ~scope_simp();
};

simp_lemmas add(type_context & tctx, simp_lemmas const & s, name const & id, expr const & e, expr const & h, unsigned priority);
simp_lemmas join(simp_lemmas const & s1, simp_lemmas const & s2);

/** \brief Get (active) simplification lemmas. */
simp_lemmas get_simp_lemmas(environment const & env);
/** \brief Get simplification lemmas in the given namespace. */
simp_lemmas get_simp_lemmas(environment const & env, name const & ns);
}
