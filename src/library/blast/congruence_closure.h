/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
struct ext_congr_lemma;
class congruence_closure {
    /*
      We maintain several equivalence relations.
      Any relation tagged as [refl], [symm] and [trans] is handled by this module.

      We use a union-find based data-structure for storing the equivalence relations.
      Each equivalence class contains one or more expressions.
      We store the additional information for each expression in the 'entry' structure.
      We use a mapping from (R, e) to 'entry', where 'R' is the equivalence relation name, and
      'e' is an expression.

      To find the equivalence class for expression 'e' with respect to equivalence relation 'R',
      we create a key (R, e) and get the associated entry. The entry has a 'm_next' field,
      that is the next element in the equivalence class containing 'e'.

      We used functional-datastructures because we must be able to create copies efficiently.
      It will be part of the blast::state object.

      Remark: only a subset of use-defined congruence rules are considered.
      We ignore user-defined congruence rules that have hypotheses and/or are contextual.
    */

    /* Equivalence class data associated with an expression 'e' */
    struct entry {
        expr           m_next;       // next element in the equivalence class.
        expr           m_root;       // root (aka canonical) representative of the equivalence class.
        expr           m_cg_root;    // root of the congruence class, it is meaningless if 'e' is not an application.
        // When 'e' was added to this equivalence class because of an equality (H : e ~ target), then we
        // store 'target' at 'm_target', and 'H' at 'm_proof'. Both fields are none if 'e' == m_root
        optional<expr> m_target;
        optional<expr> m_proof;
        unsigned       m_rank;        // rank of the equivalence class, it is meaningless if 'e' != m_root
    };

    /* Key (R, e) for the mapping (R, e) -> entry */
    struct eqc_key {
        name m_R;
        expr m_expr;
        eqc_key() {}
        eqc_key(name const & n, expr const & e):m_R(n), m_expr(e) {}
    };

    struct eqc_key_cmp {
        int operator()(eqc_key const & k1, eqc_key const & k2) const {
            int r = quick_cmp(k1.m_R, k2.m_R);
            if (r != 0) return r;
            else return is_lt(k1.m_expr, k2.m_expr, true);
        }
    };

    /* Key for the congruence set */
    struct congr_key {
        name     m_R;
        expr     m_expr;
        unsigned m_hash;
        /* We track unequivalences using congruence table.
           The idea is to store (not a = b) by putting (a = b) in the equivalence class of false.
           So, we want (a = b) and (b = a) to be the "same" key in the congruence table.
           eq and iff are ubiquitous. So, we have special treatment for them.

           \remark: the trick can be used with commutative operators, but we currently don't do it. */
        unsigned m_eq:1;       // true if m_expr is an equality
        unsigned m_iff:1;      // true if m_expr is an iff
        unsigned m_symm_rel:1; // true if m_expr is another symmetric relation.
    };

    struct congr_key_cmp {
        int operator()(congr_key const & k1, congr_key const & k2);
    };

    typedef rb_tree<expr, expr_quick_cmp>           expr_set;
    typedef rb_map<eqc_key, entry, eqc_key_cmp>     entries;
    // TODO(Leo): fix and take relation into account
    typedef rb_map<expr, expr_set, expr_quick_cmp>  parents;
    typedef rb_tree<congr_key, congr_key_cmp>       congruences;

    entries     m_entries;
    parents     m_parents;
    congruences m_congruences;

    void mk_entry_for(name const & R, expr const & e);
    void add_occurrence(name const & Rp, expr const & parent, name const & Rc, expr const & child);
    void add_congruence_table(ext_congr_lemma const & lemma, expr const & e);
    void add_eqv(name const & R, expr const & lhs, expr const & rhs, expr const & pr);

public:
    /** \brief Register expression \c e in this data-structure.
       It creates entries for each sub-expression in \c e.
       It also updates the m_parents mapping.

       We ignore the following subterms of \c e.
       1- and, or and not-applications are not inserted into the data-structures, but
          their arguments are visited.
       2- (Pi (x : A), B), the subterms A and B are not visited if B depends on x.
       3- (A -> B) is not inserted into the data-structures, but their arguments are visited
          if they are propositions.
       4- Terms containing meta-variables.
       5- The subterms of lambda-expressions.
       6- Sorts (Type and Prop). */
    void internalize(name const & R, expr const & e);
    void internalize(expr const & e);

    /** \brief Given a hypothesis H, this method will do the following based on the type of H
        1- (H : a ~ b): merge equivalence classes of 'a' and 'b', and propagate congruences.

        2- (H : not a ~ b): add the equivalence ((a ~ b) <-> false)

        3- (H : P), if P is a proposition, add the equivalence (P <-> true)

        4- (H : not P), add the equivalence (P <-> false)

        If H is none of the forms above, this method does nothing. */
    void add(hypothesis_idx hidx);

    /** \brief Return true if an inconsistency has been detected, i.e., true and false are in the same equivalence class */
    bool is_inconsistent() const;
    /** \brief Return the proof of inconsistency */
    optional<expr> get_inconsistency_proof() const;

    /** \brief Return true iff 'e1' and 'e2' are in the same equivalence class for relation \c rel_name. */
    bool is_eqv(name const & R, expr const & e1, expr const & e2) const;
    optional<expr> get_eqv_proof(name const & rel_name, expr const & e1, expr const & e2) const;

    /** \brief Return true iff `e1 ~ e2` is in the equivalence class of false for iff. */
    bool is_uneqv(name const & R, expr const & e1, expr const & e2) const;
    optional<expr> get_uneqv_proof(name const & R, expr const & e1, expr const & e2) const;

    /** \brief Return true iff \c e has been proved by this module. That is, the proposition \c e is inhabited */
    bool prove(expr const & e) const;
    optional<expr> get_proof(expr const & e) const;

    /** \brief Return true iff \c (not e) has been proved by this module. That is, the proposition \c (not e) is inhabited */
    bool disproved(expr const & e) const;
    optional<expr> get_disproof(expr const & e) const;

    bool is_congr_root(name const & R, expr const & e) const;
    bool is_root(name const & R, expr const & e) const { return get_root(R, e) == e; }
    expr get_root(name const & R, expr const & e) const;
    expr get_next(name const & R, expr const & e) const;

    /** \brief dump for debugging purposes. */
    void display() const;
    bool check_invariant() const;
};

/** \brief Auxiliary class for initializing thread-local caches */
class scope_congruence_closure {
    void * m_old_cache;
public:
    scope_congruence_closure();
    ~scope_congruence_closure();
};
}}
