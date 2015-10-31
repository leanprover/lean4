/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "kernel/expr.h"
#include "library/tactic/goal.h"
#include "library/blast/hypothesis.h"
#include "library/blast/branch.h"

namespace lean {
namespace blast {
class metavar_decl {
    // A metavariable can be assigned to a value that contains references only to the assumptions
    // that were available when the metavariable was defined.
    hypothesis_idx_set m_assumptions;
    expr               m_type;
public:
    metavar_decl() {}
    metavar_decl(hypothesis_idx_set const & a, expr const & t):
        m_assumptions(a), m_type(t) {}
    /** \brief Return true iff \c h is in the context of the this metavar declaration */
    bool contains_href(unsigned hidx) const { return m_assumptions.contains(hidx); }
    bool contains_href(expr const & h) const { return contains_href(href_index(h)); }
    expr const & get_type() const { return m_type; }
    /** \brief Make sure the declaration context of this declaration is a subset of \c other.
        \remark Return true iff the context has been modified. */
    bool restrict_context_using(metavar_decl const & other);
    hypothesis_idx_set get_assumptions() const { return m_assumptions; }
};

class state {
    typedef metavar_idx_map<metavar_decl>       metavar_decls;
    typedef metavar_idx_map<expr>               eassignment;
    typedef metavar_idx_map<level>              uassignment;
    typedef hypothesis_idx_map<metavar_idx_set> fixed_by;
    unsigned       m_next_uref_index; // index of the next universe metavariable
    uassignment    m_uassignment;
    unsigned       m_next_mref_index; // index of the next metavariable
    metavar_decls  m_metavar_decls;
    eassignment    m_eassignment;
    branch         m_main;
    // In the following mapping, each entry (h -> {m_1 ... m_n}) means that hypothesis `h` cannot be cleared
    // in any branch where the metavariables m_1 ... m_n have not been replaced with the values assigned to them.
    // That is, to be able to clear `h` in a branch `B`, we first need to check whether it
    // is contained in this mapping or not. If it is, we should check whether any of the
    // metavariables `m_1` ... `m_n` occur in `B` (this is a relatively quick check since
    // `B` contains an over-approximation of all meta-variables occuring in it (i.e., m_mvar_idxs).
    // If this check fails, then we should replace any assigned `m_i` with its value, if the intersection is still
    // non-empty, then we cannot clear `h`.
    fixed_by      m_fixed_by;

    void add_fixed_by(unsigned hidx, unsigned midx);
    unsigned add_metavar_decl(metavar_decl const & decl);
    goal to_goal(branch const &) const;

    #ifdef LEAN_DEBUG
    bool check_hypothesis(expr const & e, branch const & b, unsigned hidx, hypothesis const & h) const;
    bool check_hypothesis(branch const & b, unsigned hidx, hypothesis const & h) const;
    bool check_target(branch const & b) const;
    bool check_invariant(branch const &) const;
    #endif
public:
    state();

    level mk_uref();

    bool is_uref_assigned(level const & l) const {
        lean_assert(is_uref(l));
        return m_uassignment.contains(uref_index(l));
    }

    // u := l
    void assign_uref(level const & u, level const & l) {
        m_uassignment.insert(uref_index(u), l);
    }

    level const * get_uref_assignment(level const & l) const {
        lean_assert(is_uref_assigned(l));
        return m_uassignment.find(uref_index(l));
    }

    /** \brief Instantiate any assigned uref in \c l with its assignment.
        \remark This is not a const method because it may normalize the assignment. */
    level instantiate_urefs(level const & l);

    /** \brief Create a new metavariable using the given type and context.
        \pre ctx must be a subset of the hypotheses in the main branch. */
    expr mk_metavar(hypothesis_idx_buffer const & ctx, expr const & type);
    expr mk_metavar(hypothesis_idx_set const & ctx, expr const & type);
/** \brief Create a new metavariable using the given type.
        The context of this metavariable will be all assumption hypotheses occurring in the main branch. */
    expr mk_metavar(expr const & type);

    /** \brief Make sure the metavariable declaration context of mref1 is a
        subset of the metavariable declaration context of mref2. */
    void restrict_mref_context_using(expr const & mref1, expr const & mref2);

    bool is_mref_assigned(expr const & e) const {
        lean_assert(is_mref(e));
        return m_eassignment.contains(mref_index(e));
    }

    /** \brief Return true iff \c l contains an assigned uref */
    bool has_assigned_uref(level const & l) const;
    bool has_assigned_uref(levels const & ls) const;

    expr const * get_mref_assignment(expr const & e) const {
        lean_assert(is_mref(e));
        return m_eassignment.find(mref_index(e));
    }

    // m := e
    void assign_mref(expr const & m, expr const & e) {
        m_eassignment.insert(mref_index(m), e);
    }

    /** \brief Return true if \c e contains an assigned mref or uref */
    bool has_assigned_uref_mref(expr const & e) const;

    /** \brief Instantiate any assigned mref in \c e with its assignment.
        \remark This is not a const method because it may normalize the assignment. */
    expr instantiate_urefs_mrefs(expr const & e);

    /** \brief Add a new hypothesis to the main branch */
    expr add_hypothesis(name const & n, expr const & type, expr const & value) {
        return m_main.add_hypothesis(n, type, value);
    }

    branch & get_main_branch() { return m_main; }
    branch const & get_main_branch() const { return m_main; }

    /** \brief Add a new hypothesis to the main branch */
    expr add_hypothesis(expr const & type, expr const & value) {
        return m_main.add_hypothesis(type, value);
    }

    /** \brief Set target (aka conclusion, aka type of the goal, aka type of the term that must be synthesize in this branch)
        of the main branch */
    void set_target(expr const & type) {
        return m_main.set_target(type);
    }

    metavar_decl const * get_metavar_decl(unsigned idx) const { return m_metavar_decls.find(idx); }
    metavar_decl const * get_metavar_decl(expr const & e) const { return get_metavar_decl(mref_index(e)); }

    /** \brief Convert main branch to a goal.
        This is mainly used for pretty printing. However, in the future, we may use this capability
        to invoke the tactic framework from the blast tactic. */
    goal to_goal() const;

    void display(environment const & env, io_state const & ios) const;

    /** Auxiliary object for creating snapshots of the metavariable assignments.
        \remark The snapshots are created (and restored) in constant time */
    class assignment_snapshot {
        state &     m_state;
        uassignment m_old_uassignment;
        eassignment m_old_eassignment;
    public:
        assignment_snapshot(state & s):
            m_state(s),
            m_old_uassignment(s.m_uassignment),
            m_old_eassignment(s.m_eassignment) {}
        void restore() {
            m_state.m_uassignment = m_old_uassignment;
            m_state.m_eassignment = m_old_eassignment;
        }
    };

    #ifdef LEAN_DEBUG
    bool check_invariant() const;
    #endif
};
}}
