/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/congr_lemma_manager.h"
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
        unsigned       m_flipped:1;      // proof has been flipped
        unsigned       m_to_propagate:1; // must be propagated back to state when in equivalence class containing true/false
        unsigned       m_interpreted:1;  // true if the node should be viewed as an abstract value
        unsigned       m_size;           // number of elements in the equivalence class, it is meaningless if 'e' != m_root
        unsigned       m_mt;
        // The field m_mt is used to implement the mod-time optimization introduce by the Simplify theorem prover.
        // The basic idea is to introduce a counter gmt that records the number of heuristic instantiation that have
        // occurred in the current branch. It is incremented after each round of heuristic instantiation.
        // The field m_mt records the last time any proper descendant of of thie entry was involved in a merge.
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
            else return expr_quick_cmp()(k1.m_expr, k2.m_expr);
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
        congr_key() { m_eq = 0; m_iff = 0; m_symm_rel = 0; }
    };

    struct congr_key_cmp {
        int operator()(congr_key const & k1, congr_key const & k2) const;
    };

    typedef rb_tree<expr, expr_quick_cmp>                    expr_set;
    typedef rb_map<eqc_key, entry, eqc_key_cmp>              entries;
    typedef eqc_key     child_key;
    typedef eqc_key_cmp child_key_cmp;
    typedef eqc_key     parent_occ;
    typedef eqc_key_cmp parent_occ_cmp;
    typedef rb_tree<parent_occ, parent_occ_cmp>              parent_occ_set;
    typedef rb_map<child_key, parent_occ_set, child_key_cmp> parents;
    typedef rb_tree<congr_key, congr_key_cmp>                congruences;

    entries     m_entries;
    parents     m_parents;
    congruences m_congruences;
    list<name>  m_non_eq_relations;
    /** The congruence closure module has a mode where the root of
        each equivalence class is marked as an interpreted/abstract
        value. Moreover, in this mode proof production is disabled.
        This capability is useful for heuristic instantiation. */
    short       m_froze_partitions{false};
    short       m_inconsistent{false};
    unsigned    m_gmt{0};
    void update_non_eq_relations(name const & R);

    void register_to_propagate(expr const & e);
    void internalize_core(name const & R, expr const & e, bool toplevel, bool to_propagate);
    void process_todo(optional<expr> const & added_prop);

    int compare_symm(name const & R, expr lhs1, expr rhs1, expr lhs2, expr rhs2) const;
    int compare_root(name const & R, expr e1, expr e2) const;
    unsigned symm_hash(name const & R, expr const & lhs, expr const & rhs) const;
    congr_key mk_congr_key(ext_congr_lemma const & lemma, expr const & e) const;
    void check_iff_true(congr_key const & k);

    void mk_entry_core(name const & R, expr const & e, bool to_propagate, bool interpreted);
    void mk_entry(name const & R, expr const & e, bool to_propagate);
    void add_occurrence(name const & Rp, expr const & parent, name const & Rc, expr const & child);
    void add_congruence_table(ext_congr_lemma const & lemma, expr const & e);
    void invert_trans(name const & R, expr const & e, bool new_flipped, optional<expr> new_target, optional<expr> new_proof);
    void invert_trans(name const & R, expr const & e);
    void remove_parents(name const & R, expr const & e);
    void reinsert_parents(name const & R, expr const & e);
    void update_mt(name const & R, expr const & e);
    expr mk_iff_false_intro(expr const & proof);
    expr mk_iff_true_intro(expr const & proof);
    void add_eqv_step(name const & R, expr e1, expr e2, expr const & H, optional<expr> const & added_prop);
    void add_eqv_core(name const & R, expr const & lhs, expr const & rhs, expr const & H, optional<expr> const & added_prop);

    expr mk_congr_proof_core(name const & R, expr const & lhs, expr const & rhs) const;
    expr mk_congr_proof(name const & R, expr const & lhs, expr const & rhs) const;
    expr mk_proof(name const & R, expr const & lhs, expr const & rhs, expr const & H) const;

    void trace_eqc(name const & R, expr const & e) const;
public:
    void initialize();

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
    void internalize(name const & R, expr const & e, bool toplevel = false);
    void internalize(expr const & e);

    /** \brief Given a hypothesis H, this method will do the following based on the type of H
        1- (H : a ~ b): merge equivalence classes of 'a' and 'b', and propagate congruences.

        2- (H : not a ~ b): add the equivalence ((a ~ b) <-> false)

        3- (H : P), if P is a proposition, add the equivalence (P <-> true)

        4- (H : not P), add the equivalence (P <-> false)

        If H is none of the forms above, this method does nothing. */
    void add(hypothesis_idx hidx);
    void add(expr const & type, expr const & proof);
    /** \brief Similar to \c add but asserts the given type without proof
        \pre It can only be used after \c freeze_partitions has been invoked (i.e., proof extraction has been disabled). */
    void assume(expr const & type);

    /** \brief Assert the equivalence (R a b) with proof H. */
    void add_eqv(name const & R, expr const & a, expr const & b, expr const & H);

    /** \brief Return true if an inconsistency has been detected, i.e., true and false are in the same equivalence class */
    bool is_inconsistent() const;

    /** \brief Return the proof of inconsistency */
    optional<expr> get_inconsistency_proof() const;

    /** \brief Return true iff 'e1' and 'e2' are in the same equivalence class for relation \c R. */
    bool is_eqv(name const & R, expr const & e1, expr const & e2) const;
    optional<expr> get_eqv_proof(name const & R, expr const & e1, expr const & e2) const;

    /** \brief Return true iff `e1 ~ e2` is in the equivalence class of false for iff. */
    bool is_uneqv(name const & R, expr const & e1, expr const & e2) const;
    optional<expr> get_uneqv_proof(name const & R, expr const & e1, expr const & e2) const;

    /** \brief Return true iff \c e has been proved by this module. That is, the proposition \c e is inhabited */
    bool proved(expr const & e) const;
    optional<expr> get_proof(expr const & e) const;

    /** \brief Return true iff \c (not e) has been proved by this module. That is, the proposition \c (not e) is inhabited */
    bool disproved(expr const & e) const;
    optional<expr> get_disproof(expr const & e) const;

    bool is_congr_root(name const & R, expr const & e) const;
    bool is_root(name const & R, expr const & e) const { return get_root(R, e) == e; }
    expr get_root(name const & R, expr const & e) const;
    expr get_next(name const & R, expr const & e) const;

    /** \brief Mark the root of each equivalence class as an "abstract value"
        After this method is invoked, proof production is disabled. Moreover,
        merging two different partitions will trigger an inconsistency. */
    void freeze_partitions();

    void inc_gmt() { m_gmt++; }

    unsigned get_gmt() const { return m_gmt; }
    unsigned get_mt(name const & R, expr const & e) const;

    /** \brief dump for debugging purposes. */
    void trace() const;
    void trace_eqcs() const;
    void trace_parents() const;
    bool check_eqc(name const & R, expr const & e) const;
    bool check_invariant() const;
};

/** \brief Auxiliary class for initializing thread-local caches */
class scope_congruence_closure {
    void * m_old_cache;
public:
    scope_congruence_closure();
    ~scope_congruence_closure();
};

/** \brief Return the congruence closure object associated with the current state */
congruence_closure & get_cc();

struct ext_congr_lemma {
    /* Relation this lemma is a congruence for */
    name                 m_R;
    /* The basic congr_lemma object defined at congr_lemma_manager */
    congr_lemma          m_congr_lemma;
    /* m_rel_names is the relation congruence to be used with each child, none means child is ignored by congruence closure.
       An element is not none iff it corresponds to an Eq kind at m_congr_lemma.get_arg_kinds() */
    list<optional<name>> m_rel_names;
    /* If m_lift_needed is true, m_congr_lemma is for equality, and we need to lift to m_R. This is just a helper flag fo building
       a proof from the equivalence argument proofs. */
    unsigned             m_lift_needed:1;
    /* If m_fixed_fun is false, then we build equivalences for functions, and use generic congr lemma, and ignore m_congr_lemma.
       That is, even the function can be treated as an Eq argument. */
    unsigned             m_fixed_fun:1;
    ext_congr_lemma(congr_lemma const & H);
    ext_congr_lemma(name const & R, congr_lemma const & H, bool lift_needed);
    ext_congr_lemma(name const & R, congr_lemma const & H, list<optional<name>> const & rel_names, bool lift_needed);

    name const & get_relation() const { return m_R; }
    congr_lemma const & get_congr_lemma() const { return m_congr_lemma; }
    list<optional<name>> const & get_arg_rel_names() const { return m_rel_names; }
};

/** \brief Build an extended congruence lemma for function \c fn with \c nargs expected arguments over relation \c R.
    A subset of user-defined congruence lemmas is considered by this procedure. */
optional<ext_congr_lemma> mk_ext_congr_lemma(name const & R, expr const & fn, unsigned nargs);

void initialize_congruence_closure();
void finalize_congruence_closure();
}}
