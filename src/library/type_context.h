/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/projection.h"

namespace lean {
bool get_class_trace_instances(options const & o);
unsigned get_class_instance_max_depth(options const & o);
bool get_class_trans_instances(options const & o);

/** \brief Light-weight type inference, normalization and definitional equality.
    It is simpler and more efficient version of the kernel type checker.
    It does not generate unification constraints.
    Unification problems are eagerly solved. However, only higher-order patterns
    are supported.

    This is a generic class containing several virtual methods that must
    be implemeneted by "customers" (e.g., blast tactic).

    This class also implements type class resolution
*/
class type_context {
    struct ext_ctx;
    friend struct ext_ctx;
    environment                     m_env;
    io_state                        m_ios;
    name_generator                  m_ngen;
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

    bool is_opaque(declaration const & d) const;
    optional<expr> expand_macro(expr const & m);
    optional<expr> reduce_projection(expr const & e);
    optional<expr> norm_ext(expr const & e);
    expr whnf_core(expr const & e);
    expr unfold_name_core(expr e, unsigned h);
    expr unfold_names(expr const & e, unsigned h);
    optional<declaration> is_delta(expr const & e) const;
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

    pos_info_provider const *     m_pip;
    std::vector<pair<name, expr>> m_ci_local_instances;
    expr_struct_map<expr>         m_ci_cache;
    bool                          m_ci_multiple_instances;
    expr                          m_ci_main_mvar;
    ci_state                      m_ci_state;    // active state
    std::vector<ci_choice>        m_ci_choices;
    unsigned                      m_ci_choices_ini_sz;
    bool                          m_ci_displayed_trace_header;
    optional<pos_info>            m_ci_pos;

    // configuration options
    unsigned                      m_ci_max_depth;
    bool                          m_ci_trans_instances;
    bool                          m_ci_trace_instances;

    io_state_stream diagnostic();
    optional<name> constant_is_class(expr const & e);
    optional<name> is_full_class(expr type);
    lbool is_quick_class(expr const & type, name & result);

    optional<pair<expr, expr>> find_unsynth_metavar(expr const & e);

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
    optional<expr> check_ci_cache(expr const & type) const;
    void cache_ci_result(expr const & type, expr const & inst);
public:
    type_context(environment const & env, io_state const & ios, bool multiple_instances = false);
    virtual ~type_context();

    void set_context(list<expr> const & ctx);

    environment const & env() const { return m_env; }

    /** \brief Opaque constants are never unfolded by this procedure.
        The is_def_eq method will lazily unfold non-opaque constants.

        \remark This class always treats projections and theorems as opaque. */
    virtual bool is_extra_opaque(name const & n) const = 0;

    /** \brief Create a temporary local constant */
    virtual expr mk_tmp_local(expr const & type, binder_info const & bi = binder_info()) = 0;

    /** \brief Return true if \c e was created using \c mk_tmp_local */
    virtual bool is_tmp_local(expr const & e) const = 0;

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
        \c u, and nullptr if it is not assigned.
        \pre is_uvar(u) */
    virtual level const * get_assignment(level const & u) const = 0;

    /** \brief Return the assignment for unification variable
        \c m, and nullptr if it is not assigned.
        \pre is_mvar(u) */
    virtual expr const * get_assignment(expr const & m) const = 0;

    /** \brief Update the assignment for \c u.
        \pre is_uvar(u) */
    virtual void update_assignment(level const & u, level const & v) = 0;
    /** \brief Update the assignment for \c m.
        \pre is_mvar(m) */
    virtual void update_assignment(expr const & m, expr const & v) = 0;
    /** \brief Given a metavariable m that takes locals as arguments, this method
        should return true if m can be assigned to an abstraction of \c v.

        \remark This method should check at least if m does not occur in v,
        and if all tmp locals in v are in locals.

        The default implementation checks the following things:
         1. Any (internal) local constant occurring in v occurs in locals
         2. m does not occur in v
    */
    virtual bool validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v);

    /** \brief Return the type of a local constant (local or not).
        \remark This method allows the customer to store the type of local constants
        in a different place. */
    virtual expr infer_local(expr const & e) const = 0;

    /** \brief Return the type of a meta-variable (even if it is not a unification one) */
    virtual expr infer_metavar(expr const & e) const = 0;

    virtual level mk_uvar() = 0;

    virtual expr mk_mvar(expr const &) = 0;

    /** \brief Save the current assignment and metavariable declarations */
    virtual void push() = 0;
    /** \brief Retore assignment (inverse for push) */
    virtual void pop() = 0;
    /** \brief Keep the changes since last push */
    virtual void commit() = 0;

    /** \brief This method is invoked before failure.
        The "customer" may try to assign unassigned mvars in the given expression.
        The result is true to indicate that some metavariable has been assigned.

        The default implementation tries to invoke type class resolution to
        assign unassigned metavariables in the given terms. */
    virtual bool on_is_def_eq_failure(expr &, expr &);

    bool is_assigned(level const & u) const { return get_assignment(u) != nullptr; }
    bool is_assigned(expr const & m) const { return get_assignment(m) != nullptr; }

    bool has_assigned_uvar(level const & l) const;
    bool has_assigned_uvar(levels const & ls) const;
    bool has_assigned_uvar_mvar(expr const & e) const;

    /** \brief Instantiate assigned universe unification variables occurring in \c l */
    level instantiate_uvars(level const & l);

    /** \brief Instantiate assigned unification variables occurring in \c e */
    expr instantiate_uvars_mvars(expr const & e);

    /** \brief Put the given term in weak-head-normal-form (modulo is_opaque predicate) */
    expr whnf(expr const & e);

    /** \brief Return true if \c e is a proposition */
    bool is_prop(expr const & e);

    /** \brief Infer the type of \c e. */
    expr infer(expr const & e);

    /** \brief Return true if \c e1 and \c e2 are definitionally equal.
        When \c e1 and \c e2, this method is not as complete as the one in the kernel.
        That is, it may return false even when \c e1 and \c e2 may be definitionally equal.

        It is precise if \c e1 and \c e2 do not contain metavariables.
     */
    bool is_def_eq(expr const & e1, expr const & e2);

    /** \brief If \c type is a type class, return its name */
    optional<name> is_class(expr const & type);

    /** \brief Try to synthesize an instance of the type class \c type */
    optional<expr> mk_class_instance(expr const & type);
    optional<expr> next_class_instance();

    /** \brief Clear internal caches used to speedup computation */
    void clear_cache();

    /** \brief Update configuration options.
        Return true iff the new options do not change the behavior of the object.
        \remark We assume pretty-printing options are irrelevant. */
    bool update_options(options const & opts);

    /** \brief Return true if the local instances at \c ctx are compatible with the ones
        in the type inference object. This method is used to decide whether a type inference
        object can be reused by the elaborator. */
    bool compatible_local_instances(list<expr> const & ctx);

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
    unsigned                  m_next_local_idx;
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
    default_type_context(environment const & env, io_state const & ios,
                           list<expr> const & ctx = list<expr>(), bool multiple_instances = false);
    virtual ~default_type_context();
    virtual bool is_extra_opaque(name const & n) const { return m_not_reducible_pred(n); }
    virtual bool ignore_universe_def_eq(level const & l1, level const & l2) const;
    virtual expr mk_tmp_local(expr const & type, binder_info const & bi);
    virtual bool is_tmp_local(expr const & e) const;
    virtual bool is_uvar(level const & l) const;
    virtual bool is_mvar(expr const & e) const;
    virtual level const * get_assignment(level const & u) const;
    virtual expr const * get_assignment(expr const & m) const;
    virtual void update_assignment(level const & u, level const & v);
    virtual void update_assignment(expr const & m, expr const & v);
    virtual level mk_uvar();
    virtual expr mk_mvar(expr const &);
    virtual expr infer_local(expr const & e) const { return mlocal_type(e); }
    virtual expr infer_metavar(expr const & e) const { return mlocal_type(e); }
    virtual void push() { m_trail.push_back(m_assignment); }
    virtual void pop() { lean_assert(!m_trail.empty()); m_assignment = m_trail.back(); m_trail.pop_back(); }
    virtual void commit() { lean_assert(!m_trail.empty()); m_trail.pop_back(); }
    bool & get_ignore_if_zero() { return m_ignore_if_zero; }
};

void initialize_type_context();
void finalize_type_context();
}
