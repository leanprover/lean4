/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/head_map.h"
#include "library/vm/vm.h"
#include "library/attribute_manager.h"

namespace lean {
enum class simp_lemma_kind { Refl, Simp, Congr };
struct simp_lemma_cell;
class simp_lemma {
private:
    friend struct simp_lemma_cell;
    simp_lemma_cell * m_ptr;
    explicit simp_lemma(simp_lemma_cell * ptr);
    simp_lemma_cell * steal_ptr();
    friend simp_lemma mk_simp_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                                    list<bool> const & instances, expr const & lhs, expr const & rhs,
                                    expr const & proof, bool is_perm, unsigned priority);
    friend simp_lemma mk_rfl_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                                   list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
                                   unsigned priority);
    friend simp_lemma mk_congr_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                                     list<bool> const & instances, expr const & lhs, expr const & rhs,
                                     expr const & proof, list<expr> const & congr_hyps, unsigned priority);
public:
    simp_lemma();
    simp_lemma(simp_lemma const & s);
    simp_lemma(simp_lemma && s);
    ~simp_lemma();

    simp_lemma & operator=(simp_lemma const & s);
    simp_lemma & operator=(simp_lemma && s);

    simp_lemma_kind kind() const;
    bool is_congr() const { return kind() == simp_lemma_kind::Congr; }
    bool is_refl() const { return kind() == simp_lemma_kind::Refl; }
    name const & get_id() const;
    unsigned get_num_umeta() const;
    unsigned get_num_emeta() const;

    /** \brief Return a list containing the expression metavariables in reverse order. */
    list<expr> const & get_emetas() const;

    /** \brief Return a list of bools indicating whether or not each expression metavariable
        in <tt>get_emetas()</tt> is an instance. */
    list<bool> const & get_instances() const;

    unsigned get_priority() const;

    expr const & get_lhs() const;
    expr const & get_rhs() const;

    /** \brief Return the proof for the simp_lemma.
        \pre kind() == Simp || kind() == Congr */
    expr const & get_proof() const;

    /** \brief Return the list of hypotheses for congruence lemmas
        \pre kind() == Congr */
    list<expr> const & get_congr_hyps() const;

    bool is_permutation() const;

    format pp(formatter const & fmt) const;
};

bool operator==(simp_lemma const & r1, simp_lemma const & r2);
inline bool operator!=(simp_lemma const & r1, simp_lemma const & r2) { return !operator==(r1, r2); }

struct simp_lemma_prio_fn { unsigned operator()(simp_lemma const & s) const { return s.get_priority(); } };

typedef head_map_prio<simp_lemma, simp_lemma_prio_fn>  simp_lemma_set;

/** \brief Simplification and congruence lemmas for a given equivalence relation */
class simp_lemmas_for {
    name           m_eqv;
    simp_lemma_set m_simp_set;
    simp_lemma_set m_congr_set;
public:
    simp_lemmas_for();
    simp_lemmas_for(name const & eqv);
    bool empty() const { return m_simp_set.empty() && m_congr_set.empty(); }
    name const & get_eqv() const { return m_eqv; }
    void insert(simp_lemma const & r);
    void erase(simp_lemma const & r);
    void erase(name_set const & ids);
    void erase(buffer<name> const & ids);
    /* Return the Simp/Refl simp_lemma's for the given head index */
    list<simp_lemma> const * find(head_index const & h) const;
    void for_each(std::function<void(simp_lemma const &)> const & fn) const;
    /* Return the Congr simp_lemma's for the given head index */
    list<simp_lemma> const * find_congr(head_index const & h) const;
    void for_each_congr(std::function<void(simp_lemma const &)> const & fn) const;
};

/** \brief Collection of simplification and congruence lemmas for different equivalence relations.
    \remark Refl lemmas are use only for eq */
class simp_lemmas {
    name_map<simp_lemmas_for> m_sets; // mapping from relation name to simp_lemmas_for
public:
    bool empty() const { return m_sets.empty(); }
    void insert(name const & eqv, simp_lemma const & r);
    void erase(name const & eqv, simp_lemma const & r);
    void erase(name_set const & ids);
    void erase(buffer<name> const & ids);
    void get_relations(buffer<name> & rs) const;
    simp_lemmas_for const * find(name const & eqv) const;
    list<simp_lemma> const * find(name const & eqv, head_index const & h) const;
    void for_each(std::function<void(name const &, simp_lemma const &)> const & fn) const;
    list<simp_lemma> const * find_congr(name const & eqv, head_index const & h) const;
    void for_each_congr(std::function<void(name const &, simp_lemma const &)> const & fn) const;
    format pp(formatter const & fmt, format const & header, bool simp, bool congr) const;
    format pp_simp(formatter const & fmt, format const & header) const;
    format pp_simp(formatter const & fmt) const;
    format pp_congr(formatter const & fmt) const;
    format pp(formatter const & fmt) const;

    friend bool is_eqp(simp_lemmas const & a, simp_lemmas const & b) {
        return is_eqp(a.m_sets, b.m_sets);
    }
};

typedef unsigned simp_lemmas_token;

/* Create a token for accessing a collection of simp_lemmas that contains the given simp and congr attributes.
   The attributes are automatically registered in the system IF they have not already been registered. */
simp_lemmas_token register_simp_attribute(name const & user_name,
                                          std::initializer_list<name> const & simp_attrs,
                                          std::initializer_list<name> const & congr_attrs);

simp_lemmas get_simp_lemmas(environment const & env, simp_lemmas_token tk);
simp_lemmas get_default_simp_lemmas(environment const & env);
simp_lemmas get_simp_lemmas(environment const & env, name const & tk_name);

simp_lemmas add(type_context_old & ctx, simp_lemmas const & s, name const & id, unsigned priority);
simp_lemmas add(type_context_old & ctx, simp_lemmas const & s, name const & id, expr const & e, expr const & h, unsigned priority);
simp_lemmas add_congr(type_context_old & ctx, simp_lemmas const & s, name const & id, unsigned priority);
simp_lemmas join(simp_lemmas const & s1, simp_lemmas const & s2);

/** \brief Return true iff 'e' is of the form 'lhs rel rhs' where rel is a transitive and reflexive
    relation in 'env' */
bool is_simp_relation(environment const & env, expr const & e, expr & rel, expr & lhs, expr & rhs);

/** \brief Rewrite 'e' using the given refl lemma.
    \pre sl.is_refl() */
expr refl_lemma_rewrite(type_context_old & ctx, expr const & e, simp_lemma const & sl);

bool is_simp_lemmas(vm_obj const & o);
simp_lemmas const & to_simp_lemmas(vm_obj const & o);
vm_obj to_obj(simp_lemmas const & s);

basic_attribute const & get_refl_lemma_attribute();
bool is_rfl_lemma(expr type, expr pf);
bool is_rfl_lemma(environment const & env, name const & cname);
environment mark_rfl_lemma(environment const & env, name const & cname);

/* Return the declaration name for the simp attribute `attr_name` */
name mk_simp_attr_decl_name(name const & attr_name);

void initialize_simp_lemmas();
void finalize_simp_lemmas();
}
