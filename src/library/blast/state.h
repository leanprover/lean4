/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "kernel/expr.h"
#include "library/head_map.h"
#include "library/tactic/goal.h"
#include "library/simplifier/simp_rule_set.h"
#include "library/blast/action_result.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
typedef rb_tree<unsigned, unsigned_cmp> metavar_idx_set;
typedef hypothesis_idx_map<hypothesis> hypothesis_decls;
template<typename T> using metavar_idx_map = typename lean::rb_map<unsigned, T, unsigned_cmp>;

/** \brief Metavariable declaration in the blast proof state.
    Each declaration contains a type and the assumptions it depends on. */
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
    /** \brief When an action updates the main branch of the proof state,
        it adds a proof_step object to the proof step stack.
        The proof_step object is responsible for converting a proof for
        the new branch into a proof for the original branch.

        If the action requires multiple branches to be solved,
        the proof-step object is reponsible for creating the next branch.

        The resolve method result can be:
        1- Failed
        2- NewBranch: the current state has been updated with the next branch to
           be solved.
        3- Solved(pr): all branches have been processed and pr is the
           proof for the original branch.

        \remark Proof steps may be shared, i.e., they may occur in the
        proof-step stack of different proof state objects.
        So, resolve must not perform destructive updates.
        We enforce that by marking this method const.

        Proof-steps are usually not used when implementing forward chaining. */
    virtual action_result resolve(expr const & pr) const = 0;

    /** \brief We say a proof step is "silent" if it doesn't contribute to the
        proof depth. */
    virtual bool is_silent() const { return false; }
};

/** \brief Smart pointer for proof steps */
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

    action_result resolve(expr const & pr) const {
        lean_assert(m_ptr);
        return m_ptr->resolve(pr);
    }

    bool is_silent() const {
        lean_assert(m_ptr);
        return m_ptr->is_silent();
    }
};

/** \brief Information associated with the current branch of the proof state.
    This is essentially a mechanism for creating snapshots of the current branch. */
class branch {
    friend class state;
    typedef hypothesis_idx_map<hypothesis_idx_set> forward_deps;
    /* trick to make sure the rb_map::erase_min removes the hypothesis with biggest weight */
    struct inv_double_cmp {
        int operator()(double const & d1, double const & d2) const { return d1 > d2 ? -1 : (d1 < d2 ? 1 : 0); }
    };
    typedef rb_map<double, hypothesis_idx, inv_double_cmp>   priority_queue;
    typedef priority_queue                                   todo_queue;
    typedef priority_queue                                   rec_queue;
    // Hypothesis/facts in the current state
    hypothesis_decls   m_hyp_decls;
    // We break the set of hypotheses in m_hyp_decls in 4 sets that are not necessarily disjoint:
    //   - assumption
    //   - active
    //   - todo
    //   - dead
    //
    // The sets active and todo are disjoint. The set dead is also disjoint from the other sets.
    //
    // A hypothesis is an "assumption" if it comes from the input goal,
    // "intros" proof step, or an assumption obtained when applying an elimination step.
    //
    // A hypothesis is derived when it is obtained by forward chaining.
    // A derived hypothesis can be in the to-do or active sets.
    //
    // We say a hypothesis is in the to-do set when the blast haven't process it yet.
    hypothesis_idx_set       m_assumption;
    hypothesis_idx_set       m_active;
    todo_queue               m_todo_queue;
    rec_queue                m_rec_queue;    // priority queue for hypothesis we want to eliminate/recurse
    head_map<hypothesis_idx> m_head_to_hyps;
    forward_deps             m_forward_deps; // given an entry (h -> {h_1, ..., h_n}), we have that each h_i uses h.
    expr                     m_target;
    hypothesis_idx_set       m_target_deps;
    simp_rule_sets           m_simp_rule_sets;
};

/** \brief Proof state for the blast tactic */
class state {
    typedef metavar_idx_map<metavar_decl>          metavar_decls;
    typedef metavar_idx_map<expr>                  eassignment;
    typedef metavar_idx_map<level>                 uassignment;
    typedef list<proof_step>                       proof_steps;
    uassignment        m_uassignment;
    metavar_decls      m_metavar_decls;
    eassignment        m_eassignment;
    unsigned           m_proof_depth{0};
    proof_steps        m_proof_steps;
    branch             m_branch;

    void add_forward_dep(hypothesis_idx hidx_user, hypothesis_idx hidx_provider);
    void add_deps(expr const & e, hypothesis & h_user, hypothesis_idx hidx_user);
    void add_deps(hypothesis & h_user, hypothesis_idx hidx_user);
    void del_forward_dep(unsigned hidx_user, unsigned hidx_provider);

    expr mk_hypothesis(hypothesis_idx new_hidx, name const & n, expr const & type, optional<expr> const & value);

    unsigned add_metavar_decl(metavar_decl const & decl);
    goal to_goal(branch const &) const;

    expr mk_binding(bool is_lambda, unsigned num, expr const * hrefs, expr const & b) const;

    /** \brief Compute the weight of a hypothesis with the given type
        We use this weight to update the todo_queue. */
    double compute_weight(hypothesis_idx hidx, expr const & type);

    /** \brief This method is invoked when a hypothesis move from todo to active.
        We will update indices and data-structures (e.g., congruence closure). */
    void update_indices(hypothesis_idx hidx);

    /** \brief Remove the given hypothesis from indexing data-structures */
    void remove_from_indices(hypothesis const & h, hypothesis_idx hidx);

    void del_hypotheses(buffer<hypothesis_idx> const & to_delete, hypothesis_idx_set const & to_delete_set);
    bool safe_to_delete(buffer<hypothesis_idx> const & to_delete);

    void display_active(output_channel & out) const;

    #ifdef LEAN_DEBUG
    bool check_hypothesis(expr const & e, hypothesis_idx hidx, hypothesis const & h) const;
    bool check_hypothesis(hypothesis_idx hidx, hypothesis const & h) const;
    bool check_target() const;
    #endif
public:
    state();

    /************************
       Metavariables
    *************************/

    /** \brief Create a new metavariable using the given type and context.
        \pre ctx must be a subset of the hypotheses in the current branch. */
    expr mk_metavar(hypothesis_idx_buffer const & ctx, expr const & type);
    expr mk_metavar(hypothesis_idx_set const & ctx, expr const & type);
    /** \brief Create a new metavariable using the given type.
        The context of this metavariable will be all assumption hypotheses occurring
        in the current branch. */
    expr mk_metavar(expr const & type);
    metavar_decl const * get_metavar_decl(hypothesis_idx idx) const { return m_metavar_decls.find(idx); }
    metavar_decl const * get_metavar_decl(expr const & e) const { return get_metavar_decl(mref_index(e)); }

    /************************
       Save/Restore branch
    *************************/
    branch const & get_branch() const { return m_branch; }
    void set_branch(branch const & b) { m_branch = b; }

    /************************
       Hypotheses
    *************************/
    expr mk_hypothesis(name const & n, expr const & type, expr const & value);
    expr mk_hypothesis(expr const & type, expr const & value);
    expr mk_hypothesis(name const & n, expr const & type);
    expr mk_hypothesis(expr const & type);

    /** \brief Delete the given hypothesis and any other hypothesis that depends on it.
        The procedure is only performed if the target does not depend on the given hypothesis.
        Return true if success, and failure otherwise (target depends on hidx).

        The hypothesese objects are not really deleted, we keep them at m_hyp_decls,
        but they are removed from all indexing data-structures.
    */
    bool del_hypothesis(hypothesis_idx hidx);
    bool del_hypotheses(buffer<hypothesis_idx> const & hs);

    /** \brief Return the set of hypotheses that (directly) depend on the given one */
    hypothesis_idx_set get_direct_forward_deps(hypothesis_idx hidx) const;
    bool has_forward_deps(hypothesis_idx hidx) const { return !get_direct_forward_deps(hidx).empty(); }
    /** \brief Return true iff other hypotheses or the target type depends on hidx. */
    bool has_target_forward_deps(hypothesis_idx hidx) const {
        return has_forward_deps(hidx) || m_branch.m_target_deps.contains(hidx);
    }
    /** \brief Collect in \c result the hypotheses that (directly) depend on \c hidx and satisfy \c pred. */
    template<typename P>
    void collect_direct_forward_deps(hypothesis_idx hidx, hypothesis_idx_buffer_set & result, P && pred) {
        get_direct_forward_deps(hidx).for_each([&](hypothesis_idx d) {
                if (pred(d)) result.insert(d);
            });
    }
    /** \brief Collect in \c result the hypotheses that (directly) depend on \c hidx and satisfy \c pred. */
    void collect_direct_forward_deps(hypothesis_idx hidx, hypothesis_idx_buffer_set & result) {
        return collect_direct_forward_deps(hidx, result, [](hypothesis_idx) { return true; });
    }

    /** \brief Collect all hypothesis in \c result that depend directly or indirectly on hidx */
    void collect_forward_deps(hypothesis_idx hidx, hypothesis_idx_buffer_set & result);

    /** \brief Return true iff the hypothesis with index \c hidx_user depends on the hypothesis with index
        \c hidx_provider. */
    bool hidx_depends_on(hypothesis_idx hidx_user, hypothesis_idx hidx_provider) const;

    hypothesis const * get_hypothesis_decl(hypothesis_idx hidx) const { return m_branch.m_hyp_decls.find(hidx); }
    hypothesis const * get_hypothesis_decl(expr const & h) const { return get_hypothesis_decl(href_index(h)); }

    void for_each_hypothesis(std::function<void(hypothesis_idx, hypothesis const &)> const & fn) const { m_branch.m_hyp_decls.for_each(fn); }
    optional<hypothesis_idx> find_active_hypothesis(std::function<bool(hypothesis_idx, hypothesis const &)> const & fn) const { // NOLINT
        return m_branch.m_active.find_if([&](hypothesis_idx hidx) {
                return fn(hidx, *get_hypothesis_decl(hidx));
            });
    }

    /** \brief Activate the next hypothesis in the TODO queue, return none if the TODO queue is empty. */
    optional<hypothesis_idx> activate_hypothesis();

    /** \brief Pick next hypothesis from the rec queue */
    optional<hypothesis_idx> select_rec_hypothesis();
    void add_to_rec_queue(hypothesis_idx hidx, double w);

    /** \brief Store in \c r the hypotheses in this branch sorted by dependency depth */
    void get_sorted_hypotheses(hypothesis_idx_buffer & r) const;
    /** \brief Sort hypotheses in r */
    void sort_hypotheses(hypothesis_idx_buffer & r) const;
    void sort_hypotheses(hypothesis_idx_buffer_set & r) const;

    /** \brief Convert hypotheses indices into hrefs */
    void to_hrefs(hypothesis_idx_buffer const & hidxs, buffer<expr> & r) const;

    expr expand_hrefs(expr const & e, list<expr> const & hrefs) const;

    hypothesis_idx_set get_assumptions() const { return m_branch.m_assumption; }

    /** \brief Return (active) hypotheses whose head symbol is h or (not h) */
    list<hypothesis_idx> get_occurrences_of(head_index const & h) const;

    /** \brief Return (active) hypotheses whose head symbol is equal to the of hidx or it is the negation of */
    list<hypothesis_idx> get_head_related(hypothesis_idx hidx) const;

    /** \brief Return (active) hypotheses whose head symbol is equal to target or it is the negation of */
    list<hypothesis_idx> get_head_related() const;

    /************************
       Abstracting hypotheses
    *************************/

    expr mk_lambda(unsigned num, expr const * hrefs, expr const & b) const {
        return mk_binding(true, num, hrefs, b);
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


    /************************
       Target (aka what needs to be synthesized)
    *************************/

    /** \brief Set target (aka conclusion, aka type of the goal, aka type of the term that
        must be synthesize in the current branch) */
    void set_target(expr const & t);
    expr const & get_target() const { return m_branch.m_target; }
    /** \brief Return true iff the target depends on the given hypothesis */
    bool target_depends_on(hypothesis_idx hidx) const { return m_branch.m_target_deps.contains(hidx); }
    bool target_depends_on(expr const & h) const { return target_depends_on(href_index(h)); }

    /************************
       Proof steps
    *************************/

    void push_proof_step(proof_step const & ps) {
        if (!ps.is_silent())
            m_proof_depth++;
        m_proof_steps = cons(ps, m_proof_steps);
    }

    void push_proof_step(proof_step_cell * cell) {
        push_proof_step(proof_step(cell));
    }

    bool has_proof_steps() const {
        return static_cast<bool>(m_proof_steps);
    }

    proof_step top_proof_step() const {
        return head(m_proof_steps);
    }

    void pop_proof_step() {
        lean_assert(m_proof_steps);
        if (!head(m_proof_steps).is_silent()) {
            lean_assert(m_proof_depth > 0);
            m_proof_depth--;
        }
        m_proof_steps    = tail(m_proof_steps);
    }

    unsigned get_proof_depth() const {
        return m_proof_depth;
    }

    void clear_proof_steps() {
        m_proof_steps = list<proof_step>();
        m_proof_depth = 0;
    }

    /************************
       Assignment management
    *************************/

    bool is_uref_assigned(level const & l) const {
        return m_uassignment.contains(uref_index(l));
    }

    /* u := l */
    void assign_uref(level const & u, level const & l) {
        m_uassignment.insert(uref_index(u), l);
    }

    level const * get_uref_assignment(level const & l) const {
        return m_uassignment.find(uref_index(l));
    }

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
        return m_eassignment.find(mref_index(e));
    }

    /* m := e */
    void assign_mref(expr const & m, expr const & e) {
        m_eassignment.insert(mref_index(m), e);
    }

    /** \brief Return true if \c e contains an assigned mref or uref */
    bool has_assigned_uref_mref(expr const & e) const;

    /** \brief Instantiate any assigned uref in \c l with its assignment.
        \remark This is not a const method because it may normalize the assignment. */
    level instantiate_urefs(level const & l);

    /** \brief Instantiate any assigned mref in \c e with its assignment.
        \remark This is not a const method because it may normalize the assignment. */
    expr instantiate_urefs_mrefs(expr const & e);

    typedef std::tuple<uassignment, metavar_decls, eassignment> assignment_snapshot;
    assignment_snapshot save_assignment();
    void restore_assignment(assignment_snapshot const & s);

    /************************
       Simplification rules
    *************************/
    void set_simp_rule_sets(simp_rule_sets const & s) {
        m_branch.m_simp_rule_sets = s;
    }
    simp_rule_sets get_simp_rule_sets() const {
        return m_branch.m_simp_rule_sets;
    }

    /************************
       Debugging support
    *************************/

    /** \brief Convert current branch into a goal.
        This is mainly used for pretty printing. However, in the future, we may use this capability
        to invoke the tactic framework from the blast tactic. */
    goal to_goal() const;

    void display(environment const & env, io_state const & ios) const;

    #ifdef LEAN_DEBUG
    bool check_invariant() const;
    #endif
};
void initialize_state();
void finalize_state();
}}
