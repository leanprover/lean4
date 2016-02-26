/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <memory>
#include <vector>
#include "util/fresh_name.h"
#include "util/scoped_map.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/projection.h"

namespace lean {
unsigned get_class_instance_max_depth(options const & o);
bool get_class_trans_instances(options const & o);

/** \brief Type inference, normalization and definitional equality.
    It is similar to the kernel type checker but it also supports unification variables.

    Unification problems are eagerly solved. However, only higher-order patterns
    are supported.

    This is a generic class containing several virtual methods that must
    be implemeneted by "customers" (e.g., blast tactic).

    This class also implements type class resolution.

    Here are some notes on managing meta-variables and implementing validate_assignment.
    One issue in the elaborator and automated procedures is that we may create a meta-variable ?M
    in one context, and a unification constraint containing ?M in a different context.
    Here are two basic examples:

    1) forall (x : _) (A : Type) (y : A), x = y
       The "_" becomes a fresh meta-variable ?m, and the equality "x = y" produces the
       following unification constraint

                 ?m  =?=  A

       It is incorrect to solve this constraint by assigning ?m := A.
       The problem is that the term "A" is not available in the context where ?m was created.


    2) Consider the two following unification constraints

           (fun x, ?m) a =?= a
           (fun x, ?m) b =?= b

       If we apply beta-reduction to them, we get

           ?m  =?=  a
           ?m  =?=  b

       These simultaneous unification problem cannot be solved.

    In the Lean 0.2 elaborator, we addressed the issues above by making sure that
    only *closed terms* (terms not containing local constants)
    can be assigned to metavariables. So a metavariable that occurs in a
    context records the parameters it depends on. For example, we
    encode a "_" in the context (x : nat) (y : bool) as ?m x y,
    where ?m is a fresh metavariable.

    So, example 1) would not be solved because we cannot assign "A"
    (which is local constant aka free variable) to ?m.
    In example 2), we encode it as

           (fun x, ?m x) a =?= a
           (fun x, ?m x) b =?= b

    After applying beta-reduction to them, we get

           ?m a =?=  a
           ?m b =?=  b

    Which has the solution ?m := fun x, x

    The solution used in the Lean 0.2 elaborator is correct, but it may produce performance problems
    for procedures that have to create many meta-variables and the context is not small.
    For example, if the context contains N declarations, then the type of each meta-variable
    created will have N-nested Pi's.
    This is the case of the blast tactic, the simplifier and the type class resolution procedure.

    In the simplifier and type class resolution procedures we create many
    "temporary" meta variables and unification constraints that should be solved in the
    **same** context. So, the problems described above do not occur, and
    the solution used in the elaborator is an over-kill.

    So, type_context provides a more liberal approach. It allows "customers" of this
    class to provide their own validation mechanism for meta-variable assignments.
    In the simplifier and type class resolution, we use very basic validation.
    Given `?m x_1 ... x_n =?= t`, before assigning `?m := fun x_1 ... x_n, t`,
    we check whether ?m does not occurs in t, and whether all internal local constants
    in t occur in `x_1 ... x_n`.

    In blast, we have our own mechanism for tracking hypotheses (i.e., the representation
    of local constants in the blast search branches). This is a more efficient
    representation that doesn't require us to create N-nested Pi expressions
    whenever we want to create a meta-variable in a branch that has N hypotheses.

    In blast, the full local context is a telescope of the form

        1- (all hypotheses in the current state)
        2- (all temporary local constants created by auxiliary procedure)    Example: simplifier goes inside of a lambda.
        3- (all internal local constants created by type_context)            Example: when processing is_def_eq.
*/
class type_context : public abstract_type_context {
    struct ext_ctx;
    friend struct ext_ctx;
    environment                     m_env;
    std::unique_ptr<ext_ctx>        m_ext_ctx;
    // postponed universe constraints
    std::vector<pair<level, level>> m_postponed;
    name_map<projection_info>       m_proj_info;

    // Internal (configuration) options for customers

    /** If m_ignore_external_mvars is true, then we treat (external) expression meta-variables
        as wildcards. That is, (?M t_1 ... t_n) matches any term T. We say a meta-variable is
        external when is_mvar returns false for it, and this module can't assign it. */
    bool                            m_ignore_external_mvars;

    /** If m_check_types is true, then whenever we assign a meta-variable,
        we check whether the type of the value matches the type of the meta-variable.
        When this option is enabled, we turn on m_ignore_external_mvars while checking types.

        At this point, this option is useful only for helping us solve universe unification constraints.
        For example, consider the following unification problem
        Given:
             p   : Type.{l1}
             q   : Type.{l2}
             ?m1 : Type.{?u1}
             ?m2 : Type.{?u2}

             decidable.{max ?u1 u2} (?m1 -> ?m2)  =?=  decidable.{max l1 l2} (q -> p)

        If m_check_types is turned off, the is_def_eq implemented here produces the incorrect solution

             ?u1 := l1
             ?u2 := l2
             ?m1 := q
             ?m2 := p

        This solution is type incorrect.

             ?m1 : Type.{l1}     q  : Type.{l2}
             ?m2 : Type.{l2}     p  : Type.{l1}

        TODO(Leo,Daniel): checking types is extra overhead, and it seems unnecessary most of the time.
        We should investigate how often this kind of constraint occurs in blast.
    */
    bool                            m_check_types;

    /** Temporary flag to override/ignore the is_extra_opaque predicate.
        We use it when inferring types and we want to be sure a type is Pi-type. */
    bool                            m_relax_is_opaque;

    typedef scoped_map<expr, expr, expr_hash, std::equal_to<expr>> infer_cache;
    infer_cache m_infer_cache;

    typedef std::unordered_map<name, optional<declaration>, name_hash> is_transparent_cache;
    is_transparent_cache m_is_transparent_cache[2];

    bool is_opaque(declaration const & d) const;
    optional<declaration> is_transparent(name const & n);
    optional<expr> reduce_projection(expr const & e);
    optional<expr> norm_ext(expr const & e);
    expr whnf_core(expr const & e);
    expr unfold_name_core(expr e, unsigned h);
    expr unfold_names(expr const & e, unsigned h);
    optional<declaration> is_delta(expr const & e);
    expr whnf_core(expr e, unsigned h);

    lbool quick_is_def_eq(level const & l1, level const & l2);
    bool full_is_def_eq(level const & l1, level const & l2);
    bool is_def_eq(level const & l1, level const & l2);
    bool is_def_eq(levels const & ls1, levels const & ls2);

    lbool quick_is_def_eq(expr const & e1, expr const & e2);
    bool is_def_eq_core(expr const & e1, expr const & e2);
    bool is_def_eq_args(expr const & e1, expr const & e2);
    bool is_def_eq_binding(expr e1, expr e2);
    bool is_def_eq_eta(expr const & e1, expr const & e2);
    bool is_def_eq_proof_irrel(expr const & e1, expr const & e2);

    expr subst_mvar(expr const & e);
    bool process_assignment_core(expr const & ma, expr const & v);
    bool process_assignment(expr const & ma, expr const & v);
    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };
    reduction_status lazy_delta_reduction_step(expr & t_n, expr & s_n);
    lbool lazy_delta_reduction(expr & t_n, expr & s_n);
    reduction_status ext_reduction_step(expr & t_n, expr & s_n);
    lbool reduce_def_eq(expr & t_n, expr & s_n);

    bool process_postponed(unsigned old_sz);

    expr infer_constant(expr const & e);
    expr infer_macro(expr const & e);
    expr infer_lambda(expr e);
    expr infer_pi(expr const & e);
    expr infer_app(expr const & e);
    void ensure_sort(expr const & e, expr const & ref);
    void ensure_pi(expr const & e, expr const & ref);

    struct scope {
        type_context & m_owner;
        bool           m_keep;
        unsigned       m_postponed_sz;
        scope(type_context & o):m_owner(o), m_keep(false), m_postponed_sz(o.m_postponed.size()) { m_owner.push(); }
        ~scope() { m_owner.m_postponed.resize(m_postponed_sz); if (!m_keep) m_owner.pop(); }
        void commit() { m_postponed_sz = m_owner.m_postponed.size(); m_owner.commit(); m_keep = true; }
    };

    // Data-structures for type class resolution

    struct ci_stack_entry {
        // We only use transitive instances when we can solve the problem in a single step.
        // That is, the transitive instance does not have any instance argument, OR
        // it uses local instances to fill them.
        // We accomplish that by not considering global instances when solving
        // transitive instance subproblems.
        expr     m_mvar;
        unsigned m_depth;
        bool     m_trans_inst_subproblem;
        ci_stack_entry(expr const & m, unsigned d, bool s = false):
            m_mvar(m), m_depth(d), m_trans_inst_subproblem(s) {}
    };

    struct ci_state {
        bool                  m_trans_inst_subproblem;
        list<ci_stack_entry>  m_stack; // stack of meta-variables that need to be synthesized;
    };

    struct ci_choice {
        list<expr>            m_local_instances;
        list<name>            m_trans_instances;
        list<name>            m_instances;
        ci_state              m_state;
    };

    struct ci_choices_scope {
        type_context & m_owner;
        unsigned       m_ci_choices_sz;
        bool           m_keep{false};
        ci_choices_scope(type_context & o):m_owner(o), m_ci_choices_sz(o.m_ci_choices.size()) {}
        ~ci_choices_scope() { if (!m_keep) m_owner.restore_choices(m_ci_choices_sz); }
        void commit() { m_keep = true; }
    };

    pos_info_provider const *       m_pip;
    std::vector<pair<name, expr>>   m_ci_local_instances;
    expr_struct_map<optional<expr>> m_ci_cache;
    bool                            m_ci_multiple_instances;
    expr                            m_ci_main_mvar;
    ci_state                        m_ci_state;    // active state
    std::vector<ci_choice>          m_ci_choices;
    unsigned                        m_ci_choices_ini_sz;
    bool                            m_ci_displayed_trace_header;
    optional<pos_info>              m_ci_pos;

    /* subsingleton instance cache, we also cache failures */
    expr_struct_map<optional<expr>> m_ss_cache;

    // configuration options
    unsigned                        m_ci_max_depth;
    bool                            m_ci_trans_instances;
    bool                            m_ci_trace_instances;

    optional<name> constant_is_class(expr const & e);
    optional<name> is_full_class(expr type);
    lbool is_quick_class(expr const & type, name & result);

    optional<pair<expr, expr>> find_unsynth_metavar_at_args(expr const & e);
    optional<pair<expr, expr>> find_unsynth_metavar(expr const & e);

    expr mk_internal_local(name const & n, expr const & type, binder_info const & bi = binder_info());
    expr mk_internal_local(expr const & type, binder_info const & bi = binder_info());
    expr mk_internal_local_from_binding(expr const & b) {
        return mk_internal_local(binding_name(b), binding_domain(b), binding_info(b));
    }

    void trace(unsigned depth, expr const & mvar, expr const & mvar_type, expr const & r);
    bool try_instance(ci_stack_entry const & e, expr const & inst, expr const & inst_type, bool trans_inst);
    bool try_instance(ci_stack_entry const & e, name const & inst_name, bool trans_inst);
    list<expr> get_local_instances(name const & cname);
    bool is_ci_done() const;
    bool mk_choice_point(expr const & mvar);
    bool process_next_alt_core(ci_stack_entry const & e, list<expr> & insts);
    bool process_next_alt_core(ci_stack_entry const & e, list<name> & inst_names, bool trans_inst);
    bool process_next_alt(ci_stack_entry const & e);
    bool process_next_mvar();
    bool backtrack();
    optional<expr> search();
    optional<expr> next_solution();
    void init_search(expr const & type);
    void restore_choices(unsigned old_sz);
    optional<expr> ensure_no_meta(optional<expr> r);
    optional<expr> mk_nested_instance(expr const & type);
    bool mk_nested_instance(expr const & m, expr const & m_type);
    optional<expr> mk_class_instance_core(expr const & type);
    void cache_ci_result(expr const & type, optional<expr> const & inst);
public:
    type_context(environment const & env, options const & o, bool multiple_instances = false);
    virtual ~type_context();

    void set_local_instances(list<expr> const & insts);

    environment const & env() const { return m_env; }

    /** \brief Opaque constants are never unfolded by this procedure.
        The is_def_eq method will lazily unfold non-opaque constants.

        \remark This class always treats projections and theorems as opaque. */
    virtual bool is_extra_opaque(name const & n) const = 0;

    /** \brief This method is invoked when a term is being put in weak-head-normal-form.
        It is used to decide whether a macro should be unfolded or not. */
    virtual bool should_unfold_macro(expr const &) const { return true; }

    /** \brief Return true iff \c e is an internal local constant created by this object */
    bool is_internal_local(expr const & e) const;

    /** \brief Create a temporary local constant */
    expr mk_tmp_local(expr const & type, binder_info const & bi = binder_info());

    /** \brief Create a temporary local constant using the given pretty print name.
        The pretty printing name has not semantic significance. */
    virtual expr mk_tmp_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) override;

    /** \brief Create a temporary local constant based on the domain of the given binding (lambda/Pi) expression */
    expr mk_tmp_local_from_binding(expr const & b) {
        return mk_tmp_local(binding_name(b), binding_domain(b), binding_info(b));
    }

    /** \brief Return true if \c e was created using \c mk_tmp_local */
    bool is_tmp_local(expr const & e) const;

    /** \brief Return true if \c l represents a universe unification variable.
        \remark This is supposed to be a subset of is_meta(l).
        \remark This method is only invoked when is_meta(l) is true. */
    virtual bool is_uvar(level const & l) const = 0;

    /** \brief This method is invoked by is_def_eq for universe terms. It allows the customer
        to ignore a unification sub-problem for universe terms. */
    virtual bool ignore_universe_def_eq(level const &, level const &) const { return false; }

    /** \brief Return true if \c e represents a unification variable.
        \remark This is supposed to be a subset of is_metavar(e).
        \remark This method is only invoked when is_metavar(l) is true.
        This module will only assign a metavariable \c m when is_mvar(m) is true.
        This feature allows us to treat some (external) meta-variables as constants. */
    virtual bool is_mvar(expr const & e) const = 0;

    /** \brief Return the assignment for universe unification variable
        \c u, and none if it is not assigned.
        \pre is_uvar(u) */
    virtual optional<level> get_assignment(level const & u) const = 0;

    /** \brief Return the assignment for unification variable
        \c m, and none if it is not assigned.
        \pre is_mvar(u) */
    virtual optional<expr> get_assignment(expr const & m) const = 0;

    /** \brief Update the assignment for \c u.
        \pre is_uvar(u) */
    virtual void update_assignment(level const & u, level const & v) = 0;
    /** \brief Update the assignment for \c m.
        \pre is_mvar(m) */
    virtual void update_assignment(expr const & m, expr const & v) = 0;

    /** \brief Given a metavariable m that takes locals as arguments, this method
        should return true if m can be assigned to an abstraction of \c v.

        \remark This method should check at least if m does not occur in v, and
        whether all internal local constants in v occur in locals.
        The default implementation only checks that. */
    virtual bool validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v);
    /** \brief Given a metavariable and the value \c v that has already been abstracted.
        Check if the types match.
        \remark By checking the types we may be able to assign additional metavariables.
        The default implementation is:

        return is_def_eq_core(infer_metavar(m), infer(v)); */
    virtual bool validate_assignment_types(expr const & m, expr const & v);

    /** \brief Return the type of a local constant (local or not).
        \remark This method allows the customer to store the type of local constants
        in a different place. */
    virtual expr infer_local(expr const & e) const = 0;

    /** \brief Return the type of a meta-variable (even if it is not a unification one) */
    virtual expr infer_metavar(expr const & e) const = 0;

    virtual level mk_uvar() = 0;

    virtual expr mk_mvar(expr const &) = 0;

    /** \brief Save the current assignment and metavariable declarations */
    virtual void push_core() = 0;
    /** \brief Retore assignment (inverse for push) */
    virtual void pop_core() = 0;
    /** \brief Return the number of checkpoints created using \c push and not popped yet. */
    virtual unsigned get_num_check_points() const = 0;
    /** \brief Keep the changes since last push */
    virtual void commit() = 0;

    /** \brief This method is invoked before failure.
        The "customer" may try to assign unassigned mvars in the given expression.
        The result is true to indicate that some metavariable has been assigned.

        The default implementation tries to invoke type class resolution to
        assign unassigned metavariables in the given terms. */
    virtual bool on_is_def_eq_failure(expr const &, expr const &);

    bool try_unification_hints(expr const &, expr const &);
    struct unification_hint_fn;
    friend struct unification_hint_fn;

    bool is_assigned(level const & u) const { return static_cast<bool>(get_assignment(u)); }
    bool is_assigned(expr const & m) const { return static_cast<bool>(get_assignment(m)); }

    bool has_assigned_uvar(level const & l) const;
    bool has_assigned_uvar(levels const & ls) const;
    bool has_assigned_uvar_mvar(expr const & e) const;

    void push();
    void pop();

    /** \brief Expand macro using extension context */
    optional<expr> expand_macro(expr const & m);

    /** \brief Instantiate assigned universe unification variables occurring in \c l */
    level instantiate_uvars(level const & l);

    /** \brief Instantiate assigned unification variables occurring in \c e */
    expr instantiate_uvars_mvars(expr const & e);

    /** \brief Put the given term in weak-head-normal-form (modulo is_opaque predicate) */
    virtual expr whnf(expr const & e) override;

    /** \brief Similar to previous method but ignores the is_extra_opaque predicate. */
    virtual expr relaxed_whnf(expr const & e) override;

    /** \brief Return true if \c e is a proposition */
    bool is_prop(expr const & e);

    /** \brief Infer the type of \c e. */
    expr infer(expr const & e);

    /** \brief Put \c e in whnf, it is a Pi, then return whnf, otherwise return e */
    expr try_to_pi(expr const & e);
    /** \brief Put \c e in relaxed_whnf, it is a Pi, then return whnf, otherwise return e */
    expr relaxed_try_to_pi(expr const & e);

    /** \brief Return true if \c e1 and \c e2 are definitionally equal.
        When \c e1 and \c e2, this method is not as complete as the one in the kernel.
        That is, it may return false even when \c e1 and \c e2 may be definitionally equal.

        It is precise if \c e1 and \c e2 do not contain metavariables.
     */
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;
    /** \brief Similar to \c is_def_eq, but sets m_relax_is_opaque */
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) override;

    /** \brief Return the universe level for type A. If A is not a type return none. */
    optional<level> get_level_core(expr const & A);
    /** \brief Similar to previous method, but throws exception instead */
    level get_level(expr const & A);

    /** \brief If \c type is a type class, return its name */
    optional<name> is_class(expr const & type);

    /** \brief Try to synthesize an instance of the type class \c type */
    optional<expr> mk_class_instance(expr const & type);
    optional<expr> next_class_instance();
    /** \brief Try to synthesize an instance of (subsingleton type)
        \remark This method is virtual because we need a refinement
        at default_type_context to workaround an integration problem with the elaborator. */
    virtual optional<expr> mk_subsingleton_instance(expr const & type);

    /** \brief Given \c ma of the form <tt>?m t_1 ... t_n</tt>, (try to) assign
        ?m to (an abstraction of) v. Return true if success and false otherwise.

        \remark If ?m is already assigned, we just check if ma and v are definitionally
        equal. */
    bool assign(expr const & ma, expr const & v);
    /** \brief Similar to \c assign but sets m_relax_is_opaque */
    bool relaxed_assign(expr const & ma, expr const & v);


    /** \brief Similar to \c assign, but it replaces the existing assignment
        if the metavariable is already assigned.

        Application: for implicit instance arguments, we want the term to be the one
        generated by type class resolution even when it can be inferred by type inference. */
    bool force_assign(expr const & ma, expr const & v);
    /** \brief Similar to \c force_assign but sets m_relax_is_opaque */
    bool relaxed_force_assign(expr const & ma, expr const & v);

    /** \brief Clear all internal caches used to speedup computation */
    void clear_cache();
    /** \brief Clear internal type inference cache used to speedup computation */
    void clear_infer_cache();

    /** \brief Update configuration options.
        Return true iff the new options do not change the behavior of the object.
        \remark We assume pretty-printing options are irrelevant. */
    bool update_options(options const & opts);

    /** \brief Return true if the local instances at \c insts are compatible with the ones
        in the type inference object. This method is used to decide whether a type inference
        object can be reused by the elaborator. */
    bool compatible_local_instances(list<expr> const & insts);

    /** \brief Auxiliary object used to set position information for the type class resolution trace. */
    class scope_pos_info {
        type_context &            m_owner;
        pos_info_provider const * m_old_pip;
        optional<pos_info>        m_old_pos;
    public:
        scope_pos_info(type_context & o, pos_info_provider const * pip, expr const & pos_ref);
        ~scope_pos_info();
    };
};

/** \brief Default implementation for the generic type_context class.
    It implements a simple meta-variable assignment.

    We use this class to implement the interface with the elaborator. */
class default_type_context : public type_context {
    typedef rb_map<unsigned, level, unsigned_cmp> uassignment;
    typedef rb_map<unsigned, expr,  unsigned_cmp> eassignment;
    name_predicate            m_not_reducible_pred;

    struct assignment {
        uassignment m_uassignment;
        eassignment m_eassignment;
    };
    assignment                m_assignment;
    std::vector<assignment>   m_trail;
    unsigned                  m_next_uvar_idx;
    unsigned                  m_next_mvar_idx;

   /** \brief When m_ignore_if_zero is true, the following type-class resolution problem fails
       Given (A : Type{?u}), where ?u is a universe meta-variable created by an external module,

       ?Inst : subsingleton.{?u} A := subsingleton_prop ?M

       This case generates the unification problem

       subsingleton.{?u} A =?= subsingleton.{0} ?M

       which can be solved by assigning (?u := 0) and (?M := A)
       when the hack is enabled, the is_def_eq method in the type class module fails at the subproblem:

           ?u =?= 0

       That is, when the hack is on, type-class resolution cannot succeed by instantiating an external universe
       meta-variable with 0.
   */
    bool                      m_ignore_if_zero;

    unsigned uvar_idx(level const & l) const;
    unsigned mvar_idx(expr const & m) const;

public:
    default_type_context(environment const & env, options const & o,
                           list<expr> const & insts = list<expr>(), bool multiple_instances = false);
    virtual ~default_type_context();
    virtual bool is_extra_opaque(name const & n) const { return m_not_reducible_pred(n); }
    virtual bool ignore_universe_def_eq(level const & l1, level const & l2) const;
    virtual bool is_uvar(level const & l) const;
    virtual bool is_mvar(expr const & e) const;
    virtual optional<level> get_assignment(level const & u) const;
    virtual optional<expr> get_assignment(expr const & m) const;
    virtual void update_assignment(level const & u, level const & v);
    virtual void update_assignment(expr const & m, expr const & v);
    virtual level mk_uvar();
    virtual expr mk_mvar(expr const &);
    virtual expr infer_local(expr const & e) const { return mlocal_type(e); }
    virtual expr infer_metavar(expr const & e) const { return mlocal_type(e); }
    virtual void push_core() { m_trail.push_back(m_assignment); }
    virtual void pop_core() { lean_assert(!m_trail.empty()); m_assignment = m_trail.back(); m_trail.pop_back(); }
    virtual unsigned get_num_check_points() const { return m_trail.size(); }
    virtual void commit() { lean_assert(!m_trail.empty()); m_trail.pop_back(); }
    virtual optional<expr> mk_subsingleton_instance(expr const & type);
    virtual bool validate_assignment_types(expr const & m, expr const & v);
    // TODO(REMOVE)
    bool & get_ignore_if_zero() { return m_ignore_if_zero; }
};

/** \brief Simple normalizer */
class normalizer {
    type_context  &                   m_ctx;
    bool                              m_use_eta;
    bool                              m_eval_nested_prop;

    expr normalize_binding(expr const & e);
    optional<expr> unfold_recursor_core(expr const & f, unsigned i,
                                        buffer<unsigned> const & idxs, buffer<expr> & args, bool is_rec);
    expr normalize_app(expr const & e);
    expr normalize_macro(expr const & e);
    expr normalize(expr e);

public:
    /*
      eta == true         : enable eta reduction
      nested_prop == true : nested propositions are simplified (ignored if HoTT library)
    */
    normalizer(type_context & ctx, bool eta = true, bool nested_prop = false);
    virtual ~normalizer() {}

    optional<expr> unfold_recursor_major(expr const & f, unsigned idx, buffer<expr> & args);

    /** \brief Auxiliary predicate for controlling which subterms will be normalized. */
    virtual bool should_normalize(expr const &) const { return true; }

    environment const & env() const { return m_ctx.env(); }

    expr operator()(expr const & e) {
        return normalize(e);
    }
};

void initialize_type_context();
void finalize_type_context();
}
