/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <unordered_map>
#include "util/flet.h"
#include "util/lbool.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "kernel/pos_info_provider.h"
#include "library/projection.h"
#include "library/metavar_context.h"
#include "library/expr_pair_maps.h"
#include "library/exception.h"

namespace lean {
class class_exception : public generic_exception {
public:
    class_exception(expr const & m, char const * msg):generic_exception(m, msg) {}
};

enum class transparency_mode { All, Semireducible, Reducible, None };

/* \brief Cached information for type_context. */
class type_context_cache {
    typedef std::unordered_map<name, optional<declaration>, name_hash> transparency_cache;
    typedef std::unordered_map<name, bool, name_hash> name2bool;

    /** We use expr_cond_bi_struct_map because sometimes we want the inferred type to
        contain precise binder information (e.g., in the elaborator).
        Binder information includes the the binder annotations: {}, [], etc.

        That is, we want the type of (fun {A : Type} (a : A), a) to be (Pi {A : Type}, A -> A).

        When binder information is considered in the infer_cache, we can't reuse the
        cached value for (fun {A : Type} (a : A), a) when inferring the type of
        (fun (A : Type) (a : A), a). This is wasteful in modules such as the tactic framework.

        So, when we create a type_context_cache object we can specify whether this extra
        level of precision is required or not. */
    typedef expr_cond_bi_struct_map<expr> infer_cache;
    typedef expr_struct_map<expr> whnf_cache;
    typedef expr_struct_map<optional<expr>> instance_cache;
    typedef expr_struct_map<optional<expr>> subsingleton_cache;
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> failure_cache;

    environment                   m_env;
    options                       m_options;
    name_map<projection_info>     m_proj_info;

    /* We only cache inferred types if the metavariable assignment was not accessed.
       This restriction is sufficient to make sure the cached information can be reused
       because local declarations have unique global names, and these names
       are never reused. So, a term `t` containing locals `l_1, ..., l_n`
       will have the same type in any valid local context containing `l_1, ..., l_n`.

       \remark The inferred type does not depend on reducibility annotations. */
    infer_cache                   m_infer_cache;

    /* Mapping from name to optional<declaration>, this mapping is faster than the one
       at environment. Moreover, it takes into account constant reducibility annotations.
       We have four different modes.
       - ALL (everything is transparent).
       - SEMIREDUCIBLE (semireducible and reducible constants are considered transparent).
       - REDUCIBLE (only reducible constants are considered transparent).
       - NONE (everything is opaque).

       \remark In SEMIREDUCIBLE and REDUCIBLE modes, projections and theorems are considered
       opaque independently of annotations. In ALL mode, projections are considered opaque,
       this is not a problem since type_context implements a custom reduction rule for projections.

       The ALL mode is used for type inference where it is unacceptable to fail to infer a type.
       The SEMIREDUCIBLE mode is used for scenarios where an is_def_eq is expected to succeed
       (e.g., exact and apply tactics).
       The REDUCIBLE mode (more restrictive) is used during search (e.g., type class resolution,
       blast, etc).
       The NONE mode is used when normalizing expressions without using delta-reduction. */
    transparency_cache            m_transparency_cache[4];

    equiv_manager                 m_equiv_manager[4];

    failure_cache                 m_failure_cache[4];

    whnf_cache                    m_whnf_cache[4];

    name2bool                     m_aux_recursor_cache;

    /* We use the following approach for caching type class instances.

       Whenever a type_context object is initialized with a local_context lctx

       1) If lctx has an instance_fingerprint, then we compare with the instance_fingerprint
          stored in this cache, if they are equal, we keep m_local_instances,
          m_instance_cache and m_subsingleton_cache.

          New local instances added using methods type_context::push_local and type_context::push_let will
          be ignored.

       2) If lctx doesn't have one, we clear m_local_instances, m_instance_cache and m_subsingleton_cache.
          We also traverse lctx and collect the local instances.

          The methods type_context::push_local and type_context::push_let will flush the cache
          whenever new local instances are pushed into the local context.

          m_instance_cache and m_subsingleton_cache are flushed before the cache is returned to the
          cache manager. */
    optional<unsigned>            m_instance_fingerprint;
    list<pair<name, expr>>        m_local_instances;
    instance_cache                m_instance_cache;
    subsingleton_cache            m_subsingleton_cache;

    pos_info_provider const *     m_pip{nullptr};
    optional<pos_info>            m_ci_pos;

    /* Options */

    /* Maximum search depth when performing type class resolution. */
    unsigned                      m_ci_max_depth;
    /* See issue #1226 */
    unsigned                      m_nat_offset_cnstr_threshold;

    friend class type_context;
    friend class type_context_cache_manager;
    friend struct instance_synthesizer;
    void init(local_context const & lctx);
    bool is_transparent(transparency_mode m, declaration const & d);
    optional<declaration> is_transparent(transparency_mode m, name const & n);
    bool is_aux_recursor(name const & n);
public:
    /** When use_bi == true, the cache for inferred types take binder information into account.
        See comment above for infer_cache. */
    type_context_cache(environment const & env, options const & opts, bool use_bi = false);
    environment const & env() const { return m_env; }

    options const & get_options() const { return m_options; }

    /** \brief Auxiliary object used to set position information for the type class resolution trace. */
    class scope_pos_info {
        type_context_cache &      m_owner;
        pos_info_provider const * m_old_pip;
        optional<pos_info>        m_old_pos;
    public:
        scope_pos_info(type_context_cache & o, pos_info_provider const * pip, expr const & pos_ref);
        ~scope_pos_info();
    };
};

typedef std::shared_ptr<type_context_cache> type_context_cache_ptr;

/* \brief Type context cache managers are thread local data that we use
   to try to reuse type_context_cache objects */
class type_context_cache_manager {
    type_context_cache_ptr m_cache_ptr;
    unsigned               m_reducibility_fingerprint;
    unsigned               m_instance_fingerprint;
    environment            m_env;
    unsigned               m_max_depth;
    bool                   m_use_bi;
    type_context_cache_ptr release();
public:
    type_context_cache_manager(bool use_bi = false):m_use_bi(use_bi) {}
    type_context_cache_ptr mk(environment const & env, options const & o);
    void recycle(type_context_cache_ptr const & ptr);
};

class unification_hint;

class type_context : public abstract_type_context {
    typedef type_context_cache_ptr cache_ptr;
    typedef type_context_cache_manager cache_manager;
    typedef buffer<optional<level>> tmp_uassignment;
    typedef buffer<optional<expr>>  tmp_eassignment;
    typedef buffer<metavar_context> mctx_stack;
    enum class tmp_trail_kind { Level, Expr };
    typedef buffer<pair<tmp_trail_kind, unsigned>> tmp_trail;
    friend struct instance_synthesizer;
    struct scope_data {
        metavar_context m_mctx;
        unsigned        m_tmp_uassignment_sz;
        unsigned        m_tmp_eassignment_sz;
        unsigned        m_tmp_trail_sz;
        scope_data(metavar_context const & mctx, unsigned usz, unsigned esz, unsigned tsz):
            m_mctx(mctx), m_tmp_uassignment_sz(usz), m_tmp_eassignment_sz(esz), m_tmp_trail_sz(tsz) {}
    };
    typedef buffer<scope_data> scopes;
    typedef list<pair<name, expr>> local_instances;
    metavar_context    m_mctx;
    local_context      m_lctx;
    cache_manager *    m_cache_manager;
    cache_ptr          m_cache;
    local_instances    m_local_instances;
    /* We only cache results when m_used_assignment is false */
    bool               m_used_assignment;
    transparency_mode  m_transparency_mode;
    /* m_in_is_def_eq is a temporary flag set to true in the beginning of is_def_eq. */
    bool               m_in_is_def_eq;
    /* m_is_def_eq_depth is only used for tracing purposes */
    unsigned           m_is_def_eq_depth;
    /* This class supports temporary meta-variables "mode". In this "tmp" mode,
       is_metavar_decl_ref and is_univ_metavar_decl_ref are treated as opaque constants,
       and temporary metavariables (idx_metavar) are treated as metavariables,
       and their assignment is stored at m_tmp_eassignment and m_tmp_uassignment.

       m_tmp_eassignment and m_tmp_uassignment store assignment for temporary/idx metavars

       These assignments are only used during type class resolution and matching operations.
       They are references to stack allocated buffers provided by customers.
       They are nullptr if type_context is not in tmp_mode. */
    tmp_eassignment *  m_tmp_eassignment;
    tmp_uassignment *  m_tmp_uassignment;
    /* m_tmp_mvar_local_context contains m_lctx when tmp mode is activated.
       This is the context for all temporary meta-variables. */
    local_context      m_tmp_mvar_lctx;
    /* undo/trail stack for m_tmp_uassignment/m_tmp_eassignment */
    tmp_trail          m_tmp_trail;
    /* Stack of backtracking point (aka scope) */
    scopes             m_scopes;

    /* If m_approximate == true, then enable approximate higher-order unification
       even if we are not in tmp_mode */
    bool               m_approximate;

    /* If m_zeta, then use zeta-reduction (i.e., expand let-expressions at whnf) */
    bool               m_zeta{true};

    /* Postponed universe constraints.
       We postpone universe constraints containing max/imax. Examples:

               max 1 ?u =?= max 1 a
               2        =?= max ?u ?v

       The universe constraint postponement is effective because universe
       metavariables get assigned later. For example consider the following unification
       problem

          M.{1 3 3} L.{3} =?= M.{1 ?u ?v} L.{(max 1 ?u ?v)}

       is solved by first solving

              L.{3} =?= L.{(max 1 ?u ?v)}

       which postpones the universe constraint

                3 =?= max 1 ?u ?v

       and then solves

             M.{1 3 3} =?= M.{1 ?u ?v}

       which generates the easy constraints

                ?u =?= 3 and ?v =?= 3

       Now, the postponed contraint (3 =?= max ?u ?v) can be easily solved.

       Note that providing universe levels explicitly is not always a viable workaround.
       The problem is that unification problems like the one above are often created by
       automation (e.g., type class resolution, tactics, etc). In these situations, users
       have no way of providing the universe parameters. The alternative would be to write
       the whole definition by hand without using any form of automation.

       We also make sure any choice-point only succeeds if all postponed universe
       constraints created by it are resolved.

       We also only cache results that do not have pending postponed constraints. */
    buffer<pair<level, level>> m_postponed;
    /* If m_full_postponed is false, then postponed constraints involving max and imax
       that cannot be solved precisely are ignored. This step is approximate, and it is
       useful to skip it until we have additional information. */
    bool                       m_full_postponed{true};
    /* When m_assign_regular_uvars_in_tmp_mode is true, then in tmp_mode
       the unifier will assign regular universe metavariables.

       We *only* use this flag during type class resolution.

       It has been added for two reasons:

       1- We know have output params in type class, then when assigning
          the output param, we will also probably have to assign the associated
          metavariable.

       2- A recurrent problem we have is that a type class resolution fails
          because it cannot assign a universe metavariable even when there
          are no output parameters.
    */
    bool                       m_assign_regular_uvars_in_tmp_mode{false};

    std::function<bool(expr const & e)> const * m_unfold_pred; // NOLINT
    std::function<bool(name const & e)> const * m_transparency_pred; // NOLINT

    static bool is_equiv_cache_target(expr const & e1, expr const & e2) {
        return !has_metavar(e1) && !has_metavar(e2) && (get_weight(e1) > 1 || get_weight(e2) > 1);
    }
    equiv_manager & get_equiv_cache() { return m_cache->m_equiv_manager[static_cast<unsigned>(m_transparency_mode)]; }
    bool is_cached_equiv(expr const & e1, expr const & e2) {
        return is_equiv_cache_target(e1, e2) && get_equiv_cache().is_equiv(e1, e2);
    }
    void cache_equiv(expr const & e1, expr const & e2) {
        if (is_equiv_cache_target(e1, e2)) get_equiv_cache().add_equiv(e1, e2);
    }

    type_context_cache::failure_cache & get_failure_cache() { return m_cache->m_failure_cache[static_cast<unsigned>(m_transparency_mode)]; }
    void cache_failure(expr const & t, expr const & s);
    bool is_cached_failure(expr const & t, expr const & s);

    void init_local_instances();
    void flush_instance_cache();
    void update_local_instances(expr const & new_local, expr const & new_type);

    type_context(type_context_cache_ptr const & ptr, metavar_context const & mctx, local_context const & lctx,
                 transparency_mode m);
public:
    type_context(environment const & env, options const & o, metavar_context const & mctx, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible);
    type_context(environment const & env, options const & o, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible):
        type_context(env, o, metavar_context(), lctx, m) {}
    type_context(environment const & env, transparency_mode m = transparency_mode::Reducible):
        type_context(env, options(), metavar_context(), local_context(), m) {}
    type_context(environment const & env, options const & o, transparency_mode m = transparency_mode::Reducible):
        type_context(env, o, metavar_context(), local_context(), m) {}
    type_context(environment const & env, options const & o, metavar_context const & mctx, local_context const & lctx,
                 type_context_cache_manager & manager, transparency_mode m = transparency_mode::Reducible);
    virtual ~type_context();

    virtual environment const & env() const override { return m_cache->m_env; }
    options const & get_options() const { return m_cache->m_options; }
    local_context const & lctx() const { return m_lctx; }
    metavar_context const & mctx() const { return m_mctx; }
    expr mk_metavar_decl(local_context const & ctx, expr const & type) { return m_mctx.mk_metavar_decl(ctx, type); }
    level mk_univ_metavar_decl() { return m_mctx.mk_univ_metavar_decl(); }

    name get_unused_name(name const & prefix, unsigned & idx) const { return m_lctx.get_unused_name(prefix, idx); }
    name get_unused_name(name const & suggestion) const { return m_lctx.get_unused_name(suggestion); }

    /* note: mctx must be a descendant of m_mctx */
    void set_mctx(metavar_context const & mctx) { m_mctx = mctx; }
    /* note: env must be a descendant of m_env */
    void set_env(environment const & env);

    /* Set the instance fingerprint of the current local context.

       \remark After this method is invoked we cannot push local instances anymore
       using the method push_local. */
    void set_instance_fingerprint();

    bool is_def_eq(level const & l1, level const & l2);
    virtual expr whnf(expr const & e) override;
    virtual expr infer(expr const & e) override;
    virtual expr check(expr const & e) override;
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;

    virtual expr relaxed_whnf(expr const & e) override;
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) override;

    optional<expr> is_stuck_projection(expr const & e);
    virtual optional<expr> is_stuck(expr const &) override;

    virtual expr push_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) override;
    virtual expr push_local_from_binding(expr const & e) {
        lean_assert(is_binding(e));
        return push_local(binding_name(e), binding_domain(e), binding_info(e));
    }

    virtual void pop_local() override;
    virtual expr abstract_locals(expr const & e, unsigned num_locals, expr const * locals) override;

    /** Similar to whnf, but invokes the given predicate before unfolding constant symbols in the head.
        If pred(e') is false, then the method will not unfold definition in the head of e', and will return e'.
        This method is useful when we want to normalize the expression until we get a particular symbol as the head symbol. */
    expr whnf_head_pred(expr const & e, std::function<bool(expr const &)> const & pred); // NOLINT
    optional<expr> reduce_aux_recursor(expr const & e);
    optional<expr> reduce_projection(expr const & e);
    optional<expr> norm_ext(expr const & e) { return env().norm_ext()(e, *this); }

    /** Similar to whnf, but ignores transparency annotations, and use
        the given predicate to decide whether a constant should be unfolded or not.

        Remark: cache is not used. */
    expr whnf_transparency_pred(expr const & e, std::function<bool(name const &)> const & pred); // NOLINT

    /** \brief Put \c e in whnf, it is a Pi, then return whnf, otherwise return e */
    expr try_to_pi(expr const & e);
    /** \brief Put \c e in relaxed_whnf, it is a Pi, then return whnf, otherwise return e */
    expr relaxed_try_to_pi(expr const & e);

    /** Given a metavariable \c mvar, and local constants in \c locals, return (mvar' C) where
        C is a superset of \c locals and includes all local constants that depend on \c locals.
        \pre all local constants in \c locals are in metavariable context.
        \remark locals is updated with dependencies. */
    expr revert(buffer<expr> & locals, expr const & mvar);

    expr mk_lambda(local_context const & lctx, buffer<expr> const & locals, expr const & e);
    expr mk_pi(local_context const & lctx, buffer<expr> const & locals, expr const & e);
    expr mk_lambda(local_context const & lctx, expr const & local, expr const & e);
    expr mk_pi(local_context const & lctx, expr const & local, expr const & e);
    expr mk_lambda(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(local_context const & lctx, std::initializer_list<expr> const & locals, expr const & e);

    expr mk_lambda(buffer<expr> const & locals, expr const & e);
    expr mk_pi(buffer<expr> const & locals, expr const & e);
    expr mk_lambda(expr const & local, expr const & e);
    expr mk_pi(expr const & local, expr const & e);
    expr mk_lambda(std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(std::initializer_list<expr> const & locals, expr const & e);

    /* Add a let-decl (aka local definition) to the local context */
    expr push_let(name const & ppn, expr const & type, expr const & value);

    bool is_prop(expr const & e);
    bool is_proof(expr const & e);

    optional<expr> expand_macro(expr const & e);

    optional<name> is_class(expr const & type);
    optional<expr> mk_class_instance(expr const & type);
    optional<expr> mk_subsingleton_instance(expr const & type);
    /* Create type class instance in a different local context */
    optional<expr> mk_class_instance_at(local_context const & lctx, expr const & type);

    transparency_mode mode() const { return m_transparency_mode; }
    unsigned mode_idx() const { return static_cast<unsigned>(mode()); }

    expr eta_expand(expr const & e);

    /* Try to assign metavariables occuring in e using type class resolution */
    expr complete_instance(expr const & e);

    struct transparency_scope : public flet<transparency_mode> {
        transparency_scope(type_context & ctx, transparency_mode m):
            flet<transparency_mode>(ctx.m_transparency_mode, m) {
        }
    };

    struct approximate_scope : public flet<bool> {
        approximate_scope(type_context & ctx, bool approx = true):
            flet<bool>(ctx.m_approximate, approx) {}
    };

    struct zeta_scope : public flet<bool> {
        zeta_scope(type_context & ctx, bool val):
            flet<bool>(ctx.m_zeta, val) {}
    };

    struct nozeta_scope : public zeta_scope {
        nozeta_scope(type_context & ctx):zeta_scope(ctx, false) {}
    };

    struct full_postponed_scope : public flet<bool> {
        full_postponed_scope(type_context & ctx, bool full = true):
            flet<bool>(ctx.m_full_postponed, full) {}
    };

    struct relaxed_scope {
        transparency_scope m_transparency_scope;
        zeta_scope         m_zeta_scope;
        relaxed_scope(type_context & ctx):
            m_transparency_scope(ctx, transparency_mode::All),
            m_zeta_scope(ctx, true) {}
    };

    /* --------------------------
       Temporary assignment mode.
       It is used when performing type class resolution and matching.
       -------------------------- */
private:
    void set_tmp_mode(buffer<optional<level>> & tmp_uassignment, buffer<optional<expr>> & tmp_eassignment);
    void reset_tmp_mode();
public:
    struct tmp_mode_scope {
        type_context &          m_ctx;
        buffer<optional<level>> m_tmp_uassignment;
        buffer<optional<expr>>  m_tmp_eassignment;
        tmp_mode_scope(type_context & ctx, unsigned next_uidx = 0, unsigned next_midx = 0):m_ctx(ctx) {
            m_tmp_uassignment.resize(next_uidx, none_level());
            m_tmp_eassignment.resize(next_midx, none_expr());
            m_ctx.set_tmp_mode(m_tmp_uassignment, m_tmp_eassignment);
        }
        ~tmp_mode_scope() {
            m_ctx.reset_tmp_mode();
        }
    };
    struct tmp_mode_scope_with_buffers {
        type_context & m_ctx;
        tmp_mode_scope_with_buffers(type_context & ctx,
                                    buffer<optional<level>> & tmp_uassignment,
                                    buffer<optional<expr>> & tmp_eassignment):
            m_ctx(ctx) {
            m_ctx.set_tmp_mode(tmp_uassignment, tmp_eassignment);
        }
        ~tmp_mode_scope_with_buffers() {
            m_ctx.reset_tmp_mode();
        }
    };
    bool in_tmp_mode() const { return m_tmp_uassignment != nullptr; }
    void ensure_num_tmp_mvars(unsigned num_uvars, unsigned num_mvars);
    optional<level> get_tmp_uvar_assignment(unsigned idx) const;
    optional<expr> get_tmp_mvar_assignment(unsigned idx) const;
    optional<level> get_tmp_assignment(level const & l) const;
    optional<expr> get_tmp_assignment(expr const & e) const;
    level mk_tmp_univ_mvar();
    expr mk_tmp_mvar(expr const & type);

    /* Helper class to reset m_used_assignment flag */
    class reset_used_assignment {
        type_context & m_ctx;
        bool           m_old_used_assignment;
    public:
        reset_used_assignment(type_context & ctx):
            m_ctx(ctx),
            m_old_used_assignment(m_ctx.m_used_assignment) {
            m_ctx.m_used_assignment = false;
        }

        ~reset_used_assignment() {
            /* If m_used_assignment was set since construction time, then we keep it set.
               Otherwise, we restore the previous value. */
            if (!m_ctx.m_used_assignment) {
                m_ctx.m_used_assignment = m_old_used_assignment;
            }
        }
    };

    level mk_fresh_univ_metavar();

private:
    void init_core(transparency_mode m);
    optional<expr> unfold_definition_core(expr const & e);
    optional<expr> unfold_definition(expr const & e);
    optional<expr> try_unfold_definition(expr const & e);
    bool should_unfold_macro(expr const & e);
    expr whnf_core(expr const & e);
    optional<declaration> is_transparent(transparency_mode m, name const & n);
    optional<declaration> is_transparent(name const & n);
    bool use_zeta() const;

private:
    pair<local_context, expr> revert_core(buffer<expr> & to_revert, local_context const & ctx,
                                          expr const & type);
    expr revert_core(buffer<expr> & to_revert, expr const & mvar);
    expr mk_binding(bool is_pi, local_context const & lctx, unsigned num_locals, expr const * locals, expr const & e);

    /* ------------
       Temporary metavariable assignment.
       ------------ */
    void assign_tmp(level const & u, level const & l);
    void assign_tmp(expr const & m, expr const & v);

    /* ------------
       Uniform interface to tmp/regular metavariables
       That is, in tmp mode they access m_tmp_eassignment and m_tmp_uassignment,
       and in regular mode they access m_mctx.
       ------------ */
public:
    bool is_mvar_core(level const & l) const;
    bool is_mvar_core(expr const & e) const;
    bool is_mvar(level const & l) const;
    bool is_mvar(expr const & e) const;
    bool is_assigned(level const & l) const;
    bool is_assigned(expr const & e) const;
    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;
    void assign(level const & u, level const & l);
    void assign(expr const & m, expr const & v);
    level instantiate_mvars(level const & l);
    expr instantiate_mvars(expr const & e, bool postpone_push_delayed = false);
    /** \brief Instantiate the assigned meta-variables in the type of \c m
        \pre get_metavar_decl(m) is not none */
    void instantiate_mvars_at_type_of(expr const & m) {
        m_mctx.instantiate_mvars_at_type_of(m);
    }
    /** Clear assigned temporary metavars
        \pre in_tmp_mode() */
    void clear_tmp_eassignment();

private:
    /* ------------
       Type inference
       ------------ */
    expr infer_core(expr const & e);
    expr infer_local(expr const & e);
    expr infer_metavar(expr const & e);
    expr infer_constant(expr const & e);
    expr infer_macro(expr const & e);
    expr infer_lambda(expr e);
    optional<level> get_level_core(expr const & A);
    level get_level(expr const & A);
    expr infer_pi(expr e);
    expr infer_app(expr const & e);
    expr infer_let(expr e);

public:
    /* ------------
       is_def_eq
       ------------ */
    void push_scope();
    void pop_scope();
private:
    void commit_scope();
    class scope {
        friend class type_context;
        type_context & m_owner;
        bool           m_keep;
        unsigned       m_postponed_sz;
    public:
        scope(type_context & o):m_owner(o), m_keep(false), m_postponed_sz(o.m_postponed.size()) { m_owner.push_scope(); }
        ~scope() { m_owner.m_postponed.resize(m_postponed_sz); if (!m_keep) m_owner.pop_scope(); }
        void commit() { m_postponed_sz = m_owner.m_postponed.size(); m_owner.commit_scope(); m_keep = true; }
    };
    bool process_postponed(scope const & s);
    bool approximate();
    expr try_zeta(expr const & e);
    expr expand_let_decls(expr const & e);
    friend struct check_assignment_fn;
    optional<expr> check_assignment(buffer<expr> const & locals, expr const & mvar, expr v);
    bool process_assignment(expr const & m, expr const & v);

    optional<declaration> is_delta(expr const & e);
    enum class reduction_status { Continue, DefUnknown, DefEqual, DefDiff };

    bool solve_u_eq_max_u_v(level const & lhs, level const & rhs);
    lbool is_def_eq_core(level const & l1, level const & l2, bool partial);
    lbool partial_is_def_eq(level const & l1, level const & l2);
    bool full_is_def_eq(level const & l1, level const & l2);
    bool is_def_eq(levels const & ls1, levels const & ls2);
    bool is_def_eq_core_core(expr const & t, expr const & s);
    bool is_def_eq_core(expr const & t, expr const & s);
    bool is_def_eq_binding(expr e1, expr e2);
    expr try_to_unstuck_using_complete_instance(expr const & e);
    bool is_def_eq_args(expr const & e1, expr const & e2);
    bool is_def_eq_eta(expr const & e1, expr const & e2);
    bool is_def_eq_proof_irrel(expr const & e1, expr const & e2);
    expr elim_delayed_abstraction(expr const & e);
    lbool quick_is_def_eq(expr const & e1, expr const & e2);
    bool try_unification_hint(unification_hint const & h, expr const & e1, expr const & e2);
    bool try_unification_hints(expr const & e1, expr const & e2);
    bool is_productive(expr const & e);
    expr reduce_if_productive(expr const & t);
    lbool is_def_eq_lazy_delta(expr & t, expr & s);
    optional<pair<expr, expr>> find_unsynth_metavar(expr const & e);
    bool mk_nested_instance(expr const & m, expr const & m_type);
    friend class unification_hint_fn;

    /* Support for solving offset constraints, see issue #1226 */
    optional<unsigned> to_small_num(expr const & e);
    optional<unsigned> is_offset_term (expr const & t);
    lbool try_offset_eq_offset(expr const & t, expr const & s);
    lbool try_offset_eq_numeral(expr const & t, expr const & s);
    lbool try_numeral_eq_numeral(expr const & t, expr const & s);
    lbool try_nat_offset_cnstrs(expr const & t, expr const & s);

protected:
    virtual bool on_is_def_eq_failure(expr const & t, expr const & s);

private:
    /* ------------
       Type classes
       ------------ */
    optional<name> constant_is_class(expr const & e);
    optional<name> is_full_class(expr type);
    lbool is_quick_class(expr const & type, name & result);
    expr preprocess_class(expr const & type, buffer<expr_pair> & replacements);

public:
    /* Helper class for creating pushing local declarations into the local context m_lctx */
    class tmp_locals {
        type_context & m_ctx;
        buffer<expr>   m_locals;

        /* \brief Return true iff all locals in m_locals are let-decls */
        bool all_let_decls() const;
    public:
        tmp_locals(type_context & ctx):m_ctx(ctx) {}
        ~tmp_locals();

        type_context & ctx() { return m_ctx; }

        expr push_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) {
            expr r = m_ctx.push_local(pp_name, type, bi);
            m_locals.push_back(r);
            return r;
        }

        expr push_let(name const & name, expr const & type, expr const & value) {
            expr r = m_ctx.push_let(name, type, value);
            m_locals.push_back(r);
            return r;
        }

        expr push_local_from_binding(expr const & e) {
            lean_assert(is_binding(e));
            return push_local(binding_name(e), binding_domain(e), binding_info(e));
        }

        expr push_local_from_let(expr const & e) {
            lean_assert(is_let(e));
            return push_let(let_name(e), let_type(e), let_value(e));
        }

        unsigned size() const { return m_locals.size(); }
        expr const * data() const { return m_locals.data(); }

        buffer<expr> const & as_buffer() const { return m_locals; }

        expr mk_lambda(expr const & e) { return m_ctx.mk_lambda(m_locals, e); }
        expr mk_pi(expr const & e) { return m_ctx.mk_pi(m_locals, e); }
        expr mk_let(expr const & e) { lean_assert(all_let_decls()); return m_ctx.mk_lambda(m_locals, e); }
    };
    friend class tmp_locals;
};

class tmp_type_context : public abstract_type_context {
    type_context & m_ctx;
    buffer<optional<level>> m_tmp_uassignment;
    buffer<optional<expr>> m_tmp_eassignment;

public:
    tmp_type_context(type_context & ctx, unsigned num_umeta = 0, unsigned num_emeta = 0);
    type_context & ctx() const { return m_ctx; }

    virtual environment const & env() const override { return m_ctx.env(); }
    virtual expr infer(expr const & e) override;
    virtual expr whnf(expr const & e) override;
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;

    expr mk_lambda(buffer<expr> const & locals, expr const & e);
    expr mk_pi(buffer<expr> const & locals, expr const & e);
    expr mk_lambda(expr const & local, expr const & e);
    expr mk_pi(expr const & local, expr const & e);
    expr mk_lambda(std::initializer_list<expr> const & locals, expr const & e);
    expr mk_pi(std::initializer_list<expr> const & locals, expr const & e);

    bool is_prop(expr const & e);
    void assign(expr const & m, expr const & v);

    level mk_tmp_univ_mvar();
    expr mk_tmp_mvar(expr const & type);
    bool is_uassigned(unsigned i) const;
    bool is_eassigned(unsigned i) const;
    void clear_eassignment();
    expr instantiate_mvars(expr const & e);
};

/** Create a formatting function that can 'decode' metavar_decl_refs and local_decl_refs
    with declarations stored in mctx and lctx */
std::function<format(expr const &)>
mk_pp_ctx(environment const & env, options const & opts, metavar_context const & mctx, local_context const & lctx);

/** Create a formatting function that can 'decode' metavar_decl_refs and local_decl_refs
    with declarations stored in ctx */
std::function<format(expr const &)>
mk_pp_ctx(type_context const & ctx);

void initialize_type_context();
void finalize_type_context();
}
