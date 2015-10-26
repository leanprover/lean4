/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/environment.h"
#include "library/projection.h"

namespace lean {
/** \brief Light-weight type inference, normalization and definitional equality.
    It is simpler and more efficient version of the kernel type checker.
    It does not generate unification constraints.
    Unification problems are eagerly solved. However, only higher-order patterns
    are supported.

    This is a generic class containing several virtual methods that must
    be implemeneted by "customers" (e.g., type class resolution procedure, blast tactic).
*/
class type_inference {
    struct ext_ctx;
    friend struct ext_ctx;
    environment                     m_env;
    name_generator                  m_ngen;
    std::unique_ptr<ext_ctx>        m_ext_ctx;
    // postponed universe constraints
    std::vector<pair<level, level>> m_postponed;
    name_map<projection_info>       m_proj_info;

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
    bool assign_mvar(expr const & ma, expr const & v);
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
        type_inference & m_owner;
        bool             m_keep;
        unsigned         m_postponed_sz;
        scope(type_inference & o):m_owner(o), m_keep(false), m_postponed_sz(o.m_postponed.size()) { m_owner.push(); }
        ~scope() { m_owner.m_postponed.resize(m_postponed_sz); if (!m_keep) m_owner.pop(); }
        void commit() { m_postponed_sz = m_owner.m_postponed.size(); m_owner.commit(); m_keep = true; }
    };

public:
    type_inference(environment const & env);
    virtual ~type_inference();

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
        and if all tmp locals in v are in locals. */
    virtual bool validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v) = 0;

    /** \brief Return the type of a local constant (local or not).
        \remark This method allows the customer to store the type of local constants
        in a different place. */
    virtual expr infer_local(expr const & e) const = 0;

    /** \brief Return the type of a meta-variable (even if it is not a unification one) */
    virtual expr infer_metavar(expr const & e) const = 0;

    /** \brief Save the current assignment */
    virtual void push() = 0;
    /** \brief Retore assignment (inverse for push) */
    virtual void pop() = 0;
    /** \brief Keep the changes since last push */
    virtual void commit() = 0;

    /** \brief This method is invoked before failure.
        The "customer" may try to assign unassigned mvars in the given expression.
        The result is true to indicate that some metavariable has been assigned. */
    virtual bool on_is_def_eq_failure(expr &, expr &) { return false; }

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

    /** \brief Clear internal caches used to speedup computation */
    void clear_cache();
};

void initialize_type_inference();
void finalize_type_inference();
}
