/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/metavar_context.h"

namespace lean {
enum class transparent_mode { ALL, SEMIREDUCIBLE, REDUCIBLE, NONE };

/* \brief Cached information for type_context. */
class type_context_cache {
    typedef std::unordered_map<name, optional<declaration>, name_hash> transparent_cache;
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

    /* Cache for whnf (without delta). As in m_infer_cache, we only cache results if the
       metavariable assignment was not used. */
    whnf_cache                    m_whnf_cache;

    /* Mapping from name to optional<declaration>, this mapping is faster than the one
       at environment. Moreover, it takes into account constant reducibility annotations.
       We have four different modes.
       - ALL (everything is transparent).
       - SEMIREDUCIBLE (semireducible and reducible constants are considered transparent).
       - REDUCIBLE (only reducible constants are considered transparent).
       - NONE (everything is opaque).

       \remark In SEMIREDUCIBLE and REDUCIBLE modes, projections and theorems are considered
       opaque independently of annotations. In ALL mode, projections are considered opaque.

       The ALL mode is used for type inference where it is unacceptable to fail to infer a type.
       The SEMIREDUCIBLE mode is used for scenarios where an is_def_eq is expected to succeed
       (e.g., exact and apply tactics).
       The REDUCIBLE mode (more restrictive) is used during search (e.g., type class resolution,
       blast, etc).
       The NONE mode is used when normalizing expressions without using delta-reduction. */
    transparent_cache             m_transparent_cache[4];

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

    friend class type_context;
    void init(local_context const & lctx);
public:
    type_context_cache(environment const & env, options const & opts);
};

class type_context : public abstract_type_context {
    typedef type_context_cache cache;
    local_context     m_lctx;
    metavar_context & m_mctx;
    cache *           m_cache;
    bool              m_cache_owner;
    transparent_mode  m_mode;
public:
    type_context(metavar_context & mctx, local_context const & lctx, type_context_cache & cache,
                 transparent_mode m = transparent_mode::REDUCIBLE);
    type_context(environment const & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                 transparent_mode m = transparent_mode::REDUCIBLE);
    virtual ~type_context();

    virtual environment const & env() const;
    virtual expr whnf(expr const & e);
    virtual expr infer(expr const & e);
    virtual expr check(expr const & e);
    virtual bool is_def_eq(expr const & e1, expr const & e2);

    virtual expr relaxed_whnf(expr const & e);
    virtual bool relaxed_is_def_eq(expr const & e1, expr const & e2);

    virtual optional<expr> is_stuck(expr const &);
    virtual name get_local_pp_name(expr const & e) const;

    virtual bool on_is_def_eq_failure(expr const &, expr const &);

    bool is_prop(expr const & e);

    optional<expr> mk_class_instance(expr const & type);
    optional<expr> mk_subsingleton_instance(expr const & type);
};
}
