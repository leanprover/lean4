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

namespace lean {
namespace blast {
typedef rb_tree<unsigned, unsigned_cmp> metavar_idx_set;
typedef hypothesis_idx_map<hypothesis> context;

template<typename T>
using metavar_idx_map = typename lean::rb_map<unsigned, T, unsigned_cmp>;

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

class proof_step_cell {
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc() { delete this; }
public:
    virtual ~proof_step_cell() {}
    /** \brief Every proof-step must provide a resolve method.
        When the branch created by the proof-step is closed,
        a proof pr is provided, and the proof-step can perform two operations
        1- setup the next branch and return none_expr
        2- finish and return a new proof */
    virtual optional<expr> resolve(state & s, expr const & pr) = 0;
};

class proof_step {
    proof_step_cell * m_ptr;
public:
    proof_step():m_ptr(nullptr) {}
    proof_step(proof_step_cell * c):m_ptr(c) { m_ptr->inc_ref(); }
    proof_step(proof_step const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    proof_step(proof_step && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~proof_step() { if (m_ptr) m_ptr->dec_ref(); }
    proof_step & operator=(proof_step const & s) { LEAN_COPY_REF(s); }
    proof_step & operator=(proof_step && s) { LEAN_MOVE_REF(s); }

    optional<expr> resolve(state & s, expr const & pr) {
        lean_assert(m_ptr);
        return m_ptr->resolve(s, pr);
    }
};

class state {
    typedef hypothesis_idx_map<hypothesis_idx_set> forward_deps;
    typedef rb_map<double, unsigned, double_cmp>   todo_queue;
    typedef metavar_idx_map<metavar_decl>          metavar_decls;
    typedef metavar_idx_map<expr>                  eassignment;
    typedef metavar_idx_map<level>                 uassignment;
    typedef hypothesis_idx_map<metavar_idx_set>    fixed_by;
    typedef list<proof_step>                       proof_steps;
    uassignment        m_uassignment;
    metavar_decls      m_metavar_decls;
    eassignment        m_eassignment;
    // In the following mapping, each entry (h -> {m_1 ... m_n}) means that hypothesis `h` cannot be cleared
    // in any branch where the metavariables m_1 ... m_n have not been replaced with the values assigned to them.
    // That is, to be able to clear `h` in a branch `B`, we first need to check whether it
    // is contained in this mapping or not. If it is, we should check whether any of the
    // metavariables `m_1` ... `m_n` occur in `B` (this is a relatively quick check since
    // `B` contains an over-approximation of all meta-variables occuring in it (i.e., m_mvar_idxs).
    // If this check fails, then we should replace any assigned `m_i` with its value, if the intersection is still
    // non-empty, then we cannot clear `h`.
    fixed_by           m_fixed_by;
    unsigned           m_depth{0};
    proof_steps        m_proof_steps;
    // Hypothesis/facts in the current state
    context            m_context;
    // We break the set of hypotheses in m_context in 3 sets that are not necessarily disjoint:
    //   - assumption
    //   - active
    //   - todo
    //
    // The sets active and todo are disjoint.
    //
    // A hypothesis is an "assumption" if it comes from the input goal,
    // "intros" proof step, or an assumption obtained when applying an elimination step.
    //
    // A hypothesis is derived when it is obtained by forward chaining.
    // A derived hypothesis can be in the to-do or active sets.
    //
    // We say a hypothesis is in the to-do set when the blast haven't process it yet.
    hypothesis_idx_set m_assumption;
    hypothesis_idx_set m_active;
    todo_queue         m_todo_queue;
    forward_deps       m_forward_deps; // given an entry (h -> {h_1, ..., h_n}), we have that each h_i uses h.
    expr               m_target;
    hypothesis_idx_set m_target_deps;
    metavar_idx_set    m_mvar_idxs;

    void add_forward_dep(unsigned hidx_user, unsigned hidx_provider);
    void add_deps(expr const & e, hypothesis & h_user, unsigned hidx_user);
    void add_deps(hypothesis & h_user, unsigned hidx_user);

    /** \brief Compute the weight of a hypothesis with the given type
        We use this weight to update the todo_queue. */
    double compute_weight(unsigned hidx, expr const & type);

    /** \brief This method is invoked when a hypothesis move from todo to active.

        We will update indices and data-structures (e.g., congruence closure). */
    void update_indices(unsigned hidx);

    expr add_hypothesis(unsigned new_hidx, name const & n, expr const & type, expr const & value);


    void add_fixed_by(unsigned hidx, unsigned midx);
    unsigned add_metavar_decl(metavar_decl const & decl);
    goal to_goal(branch const &) const;

    expr mk_binding(bool is_lambda, unsigned num, expr const * hrefs, expr const & b) const;

    #ifdef LEAN_DEBUG
    bool check_hypothesis(expr const & e, unsigned hidx, hypothesis const & h) const;
    bool check_hypothesis(unsigned hidx, hypothesis const & h) const;
    bool check_target() const;
    #endif
public:
    state();

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

    expr add_hypothesis(name const & n, expr const & type, expr const & value);
    expr add_hypothesis(expr const & type, expr const & value);

    /** \brief Return true iff the hypothesis with index \c hidx_user depends on the hypothesis with index
        \c hidx_provider. */
    bool hidx_depends_on(unsigned hidx_user, unsigned hidx_provider) const;

    hypothesis const * get(unsigned hidx) const { return m_context.find(hidx); }
    hypothesis const * get(expr const & h) const {
        lean_assert(is_href(h));
        return get(href_index(h));
    }
    void for_each_hypothesis(std::function<void(unsigned, hypothesis const &)> const & fn) const { m_context.for_each(fn); }
    optional<unsigned> find_active_hypothesis(std::function<bool(unsigned, hypothesis const &)> const & fn) const { // NOLINT
        return m_active.find_if([&](unsigned hidx) {
                return fn(hidx, *get(hidx));
            });
    }

    /** \brief Activate the next hypothesis in the TODO queue, return none if the TODO queue is empty. */
    optional<unsigned> activate_hypothesis();

    /** \brief Store in \c r the hypotheses in this branch sorted by depth */
    void get_sorted_hypotheses(hypothesis_idx_buffer & r) const;

    /** \brief Set target (aka conclusion, aka type of the goal, aka type of the term that
        must be synthesize in the current branch) */
    void set_target(expr const & t);
    expr const & get_target() const { return m_target; }
    /** \brief Return true iff the target depends on the given hypothesis */
    bool target_depends_on(expr const & h) const { return m_target_deps.contains(href_index(h)); }

    bool has_mvar(expr const & e) const { return m_mvar_idxs.contains(mref_index(e)); }

    expr expand_hrefs(expr const & e, list<expr> const & hrefs) const;

    hypothesis_idx_set get_assumptions() const { return m_assumption; }

    metavar_decl const * get_metavar_decl(unsigned idx) const { return m_metavar_decls.find(idx); }
    metavar_decl const * get_metavar_decl(expr const & e) const { return get_metavar_decl(mref_index(e)); }

    /** \brief Convert current branch into a goal.
        This is mainly used for pretty printing. However, in the future, we may use this capability
        to invoke the tactic framework from the blast tactic. */
    goal to_goal() const;

    void display(environment const & env, io_state const & ios) const;

    class assignment_snapshot {
        friend class state;
        uassignment        m_uassignment;
        metavar_decls      m_metavar_decls;
        eassignment        m_eassignment;
        assignment_snapshot(uassignment const & u, metavar_decls const & decls, eassignment const & e):
            m_uassignment(u), m_metavar_decls(decls), m_eassignment(e) {}
    public:
    };

    assignment_snapshot save_assignment();
    void restore_assignment(assignment_snapshot const & s);

    void push_proof_step(proof_step const & ps) {
        m_depth++;
        m_proof_steps = cons(ps, m_proof_steps);
    }

    bool has_proof_steps() const {
        return static_cast<bool>(m_proof_steps);
    }

    proof_step top_proof_step() const {
        return head(m_proof_steps);
    }

    void pop_proof_step() {
        lean_assert(m_proof_steps);
        m_depth--;
        m_proof_steps = tail(m_proof_steps);
    }

    unsigned get_depth() const { return m_depth; }

    expr mk_lambda(unsigned num, expr const * hrefs, expr const & b) const {
        return mk_binding(false, num, hrefs, b);
    }
    expr mk_pi(unsigned num, expr const * hrefs, expr const & b) const {
        return mk_binding(false, num, hrefs, b);
    }
    expr mk_lambda(buffer<expr> const & hrefs, expr const & b) const {
        return mk_lambda(hrefs.size(), hrefs.data(), b);
    }
    expr mk_pi(buffer<expr> const & hrefs, expr const & b) const {
        return mk_pi(hrefs.size(), hrefs.data(), b);
    }
    expr mk_lambda(list<expr> const & hrefs, expr const & b) const;
    expr mk_pi(list<expr> const & hrefs, expr const & b) const;

    #ifdef LEAN_DEBUG
    bool check_invariant() const;
    #endif
};
void initialize_state();
void finalize_state();
}}
