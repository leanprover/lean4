/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <unordered_map>
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "kernel/expr_maps.h"
#include "library/projection.h"
#include "library/metavar_context.h"

namespace lean {
enum class transparency_mode { All, Semireducible, Reducible, None };

/* \brief Cached information for type_context. */
class type_context_cache {
    typedef std::unordered_map<name, optional<declaration>, name_hash> transparency_cache;
    typedef expr_struct_map<expr> infer_cache;
    typedef expr_map<expr>        whnf_cache;
    typedef expr_struct_map<optional<expr>> instance_cache;
    typedef expr_struct_map<optional<expr>> subsingleton_cache;
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

    /* We have two modes for caching type class instances.

       In the default mode (m_frozen_mode == false), whenever a type_context object is
       initialized with a local_context, we reset m_local_instances_initialized flag.
       and store a copy of the initial local_context. Then, the first time type class resolution
       is invoked, we collect local_instances, if they are equal to the ones in m_local_instances,
       we do nothing. Otherwise, we reset m_local_instances with the new local_instances, and
       reset the cache m_local_instances.

       When frozen mode is set, we reset m_local_instances_initialized, the instance cache,
       and the vector local_instances. Then, whenever a type_context object is created
       (and debugging code is enabled) we store a copy of the initial local context.
       Then, whenever type class resolution is invoked and m_local_instances_initialized is false,
       we copy the set of frozen local_decls instances to m_local_instances.
       If m_local_instances_initialized is true, and we are in debug mode, then
       we check if the froze local_decls instances in the initial local context are indeed
       equal to the ones in m_local_instances. If they are not, it is an assertion violation.

       We use the same cache policy for m_subsingleton_cache. */
    bool                          m_frozen_mode;
    bool                          m_local_instances_initialized;
    local_context                 m_init_local_context;
    std::vector<pair<name, expr>> m_local_instances;
    instance_cache                m_instance_cache;
    subsingleton_cache            m_subsingleton_cache;

    /* Options */

    /* Maximum search depth when performing type class resolution. */
    unsigned                      m_ci_max_depth;


    friend class type_context;
    void init(local_context const & lctx);
    bool is_transparent(transparency_mode m, declaration const & d);
    optional<declaration> is_transparent(transparency_mode m, name const & n);
    bool should_unfold_macro(expr const & e);
public:
    type_context_cache(environment const & env, options const & opts);
};

class type_context : public abstract_type_context {
    typedef type_context_cache cache;
    typedef buffer<optional<level>> tmp_uassignment;
    typedef buffer<optional<expr>>  tmp_eassignment;
    typedef buffer<metavar_context> mctx_stack;
    enum class tmp_trail_kind { Level, Expr };
    typedef buffer<pair<tmp_trail_kind, unsigned>> tmp_trail;
    struct scope_data {
        metavar_context m_mctx;
        unsigned        m_tmp_uassignment_sz;
        unsigned        m_tmp_eassignment_sz;
        unsigned        m_tmp_trail_sz;
        scope_data(metavar_context const & mctx, unsigned usz, unsigned esz, unsigned tsz):
            m_mctx(mctx), m_tmp_uassignment_sz(usz), m_tmp_eassignment_sz(esz), m_tmp_trail_sz(tsz) {}
    };
    typedef buffer<scope_data> scopes;

    metavar_context &  m_mctx;
    local_context      m_lctx;
    cache *            m_cache;
    bool               m_cache_owner;
    /* We only cache results when m_used_assignment is false */
    bool               m_used_assignment;
    transparency_mode  m_transparency_mode;
    /* When m_match_mode is true, then is_metavar_decl_ref and is_univ_metavar_decl_ref are treated
       as opaque constants, and temporary metavariables (idx_metavar) are treated as metavariables,
       and their assignment is stored at m_tmp_eassignment and m_tmp_uassignment. */
    bool               m_tmp_mode;
    /* m_tmp_mvar_local_context contains m_lctx when tmp mode is activated.
       This is the context for all temporary meta-variables. */
    local_context      m_tmp_mvar_lctx;
    /* m_tmp_eassignment and m_tmp_uassignment store assignment for temporary/idx metavars

       These assignments are only used during type class resolution and matching operations. */
    tmp_eassignment    m_tmp_eassignment;
    tmp_uassignment    m_tmp_uassignment;
    /* undo/trail stack for m_tmp_uassignment/m_tmp_eassignment */
    tmp_trail          m_tmp_trail;
    /* Stack of backtracking point (aka scope) */
    scopes             m_scopes;

public:
    type_context(metavar_context & mctx, local_context const & lctx, type_context_cache & cache,
                 transparency_mode m = transparency_mode::Reducible);
    /* Constructor for creating a type_context with a temporary type_context_cache object. */
    type_context(environment const & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                 transparency_mode m = transparency_mode::Reducible);
    virtual ~type_context();

    virtual environment const & env() const override { return m_cache->m_env; }

    bool is_def_eq(level const & l1, level const & l2);
    virtual expr whnf(expr const & e) override;
    virtual expr infer(expr const & e) override;
    virtual expr check(expr const & e) override;
    virtual bool is_def_eq(expr const & e1, expr const & e2) override;

    virtual expr relaxed_whnf(expr const & e) override;
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2) override;

    virtual optional<expr> is_stuck(expr const &) override;
    virtual name get_local_pp_name(expr const & e) const override;

    virtual expr push_local(name const & pp_name, expr const & type, binder_info const & bi = binder_info()) override;
    virtual void pop_local() override;
    virtual expr abstract_locals(expr const & e, unsigned num_locals, expr const * locals) override;

    /** Given a metavariable \c mvar, and local constants in \c locals, return (mvar' C) where
        C is a superset of \c locals and includes all local constants that depend on \c locals.
        \pre all local constants in \c locals are in metavariable context. */
    expr revert(unsigned num, expr const * locals, expr const & mvar);

    expr mk_lambda(buffer<expr> const & locals, expr const & e);
    expr mk_pi(buffer<expr> const & locals, expr const & e);

    /* Add a let-decl (aka local definition) to the local context */
    expr push_let(name const & ppn, expr const & type, expr const & value) {
        return m_lctx.mk_local_decl(ppn, type, value);
    }

    bool is_prop(expr const & e);

    optional<expr> mk_class_instance(expr const & type);
    optional<expr> mk_subsingleton_instance(expr const & type);

    /* --------------------------
       Temporary assignment mode.
       It is used when performing type class resolution and matching.
       -------------------------- */
    void set_tmp_mode(unsigned next_uidx = 0, unsigned next_midx = 0);
    optional<level> get_tmp_uvar_assignment(unsigned idx) const;
    optional<expr> get_tmp_mvar_assignment(unsigned idx) const;
    optional<level> get_tmp_assignment(level const & l) const;
    optional<expr> get_tmp_assignment(expr const & e) const;

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

private:
    void init_core(transparency_mode m);
    optional<expr> reduce_projection(expr const & e);
    bool should_unfold_macro(expr const & e);
    optional<expr> expand_macro(expr const & e);
    expr whnf_core(expr const & e);
    optional<declaration> is_transparent(name const & n);

private:
    pair<local_context, expr> revert_core(unsigned num, expr const * locals, local_context const & ctx,
                                          expr const & type, buffer<expr> & reverted);
    expr revert_core(unsigned num, expr const * locals, expr const & mvar, buffer<expr> & reverted);
    void restrict_metavars_context(expr const & e, unsigned num_locals, expr const * locals);
    void restrict_metavars_context(local_decl const & d, unsigned num_locals, expr const * locals);
    expr mk_binding(bool is_pi, unsigned num_locals, expr const * locals, expr const & e);

    /* ------------
       Temporary metavariable assignment.
       ------------ */
    void assign_tmp(level const & u, level const & l);
    void assign_tmp(expr const & m, expr const & v);

    level mk_tmp_univ_mvar();
    expr mk_tmp_mvar(expr const & type);

    /* ------------
       Uniform interface to tmp/regular metavariables
       That is, in tmp mode they access m_tmp_eassignment and m_tmp_uassignment,
       and in regular mode they access m_mctx.
       ------------ */
public:
    bool is_mvar(level const & l) const;
    bool is_mvar(expr const & e) const;
    bool is_assigned(level const & l) const;
    bool is_assigned(expr const & e) const;
    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;
    void assign(level const & u, level const & l);
    void assign(expr const & m, expr const & v);

private:
    level instantiate(level const & l);
    expr instantiate(expr const & l);

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

private:
    /* ------------
       is_def_eq
       ------------ */
    void push_scope();
    void pop_scope();
    void commit_scope();
    struct scope {
        type_context & m_owner;
        bool           m_keep;
        scope(type_context & o):m_owner(o), m_keep(false) { m_owner.push_scope(); }
        ~scope() { if (!m_keep) m_owner.pop_scope(); }
        void commit() { m_owner.commit_scope(); m_keep = true; }
    };

    bool approximate();
    expr try_zeta(expr const & e);
    expr expand_let_decls(expr const & e);
    bool process_assignment(expr const & m, expr const & v);

    optional<declaration> is_delta(expr const & e);

    bool is_def_eq(levels const & ls1, levels const & ls2);
    bool is_def_eq_core(expr const & t, expr const & s);
    bool is_def_eq_binding(expr e1, expr e2);
    bool is_def_eq_args(expr const & e1, expr const & e2);
    bool is_def_eq_eta(expr const & e1, expr const & e2);
    bool is_def_eq_proof_irrel(expr const & e1, expr const & e2);

public:
    /* Helper class for creating pushing local declarations into the local context m_lctx */
    class tmp_locals {
        type_context & m_ctx;
        buffer<expr>   m_locals;
    public:
        tmp_locals(type_context & ctx):m_ctx(ctx) {}
        ~tmp_locals();

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

        unsigned size() const { return m_locals.size(); }
        expr const * data() const { return m_locals.data(); }

        buffer<expr> const & as_buffer() const { return m_locals; }
    };
};
}
