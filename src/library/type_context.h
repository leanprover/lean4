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
    struct scope {
        bool     m_tmp;
        unsigned m_uassignment_sz;
        unsigned m_eassignment_sz;
        unsigned m_tmp_trail_sz;
    };
    typedef buffer<scope> scopes;

    metavar_context &  m_mctx;
    local_context      m_lctx;
    cache *            m_cache;
    bool               m_cache_owner;
    /* We only cache results when m_used_assignment is false */
    bool               m_used_assignment;
    transparency_mode  m_transparency_mode;
    /* We create a backtracking point (aka scope) whenever performing case-analysis in
       the is_def_eq method. The m_mctx_stack is used to save the content of m_mctx.
       Recall that m_mctx is implemented using datastructures with O(1) copy methods.

       \remark We only need to save a copy on this stack when type_context is not in
       tmp/match mode. */
    mctx_stack         m_mctx_stack;
    /* When m_match_mode is true, then is_metavar_decl_ref and is_univ_metavar_decl_ref are treated
       as opaque constants, and temporary metavariables (idx_metavar) are treated as metavariables,
       and their assignment is stored at m_tmp_eassignment and m_tmp_uassignment. */
    bool               m_tmp_mode;
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
    optional<expr> expand_macro(expr const & e);
    expr whnf_core(expr const & e);
    optional<declaration> is_transparent(name const & n);

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
    bool is_uvar(level const & l) const;
    bool is_mvar(expr const & e) const;
    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;
    void assign(level const & u, level const & l);
    void assign(expr const & m, expr const & v);
    level instantiate(level const & l);


    bool is_def_eq(levels const & ls1, levels const & ls2);
    optional<declaration> is_delta(expr const & e);
};
}
