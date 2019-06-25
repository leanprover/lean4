/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include <unordered_set>
#include "util/name_hash_map.h"
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "library/expr_unsigned_map.h"
#include "library/expr_pair_maps.h"
#include "library/abstract_context_cache.h"

namespace lean {
class context_cache : public context_cacheless {
    typedef name_hash_map<optional<constant_info>> transparency_cache;
    typedef name_hash_map<bool> name2bool;

    /** We use expr_cond_bi_struct_map because sometimes we want the inferred type to
        contain precise binder information (e.g., in the elaborator).
        Binder information includes the the binder annotations: {}, [], etc.

        That is, we want the type of (fun {A : Type} (a : A), a) to be (Pi {A : Type}, A -> A).

        When binder information is considered in the infer_cache, we can't reuse the
        cached value for (fun {A : Type} (a : A), a) when inferring the type of
        (fun (A : Type) (a : A), a). This is wasteful in modules such as the tactic framework.

        So, when we create a type_context_old_cache object we can specify whether this extra
        level of precision is required or not. */
    typedef expr_cond_bi_map<expr> infer_cache;
    typedef expr_map<expr> whnf_cache;
    typedef expr_map<optional<expr>> instance_cache;
    typedef expr_map<optional<expr>> subsingleton_cache;
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> failure_cache;

    /* Remark: we only cache inferred types if the metavariable assignment was not accessed.
       This restriction is sufficient to make sure the cached information can be reused. */
    infer_cache                   m_infer_cache;

    /* Mapping from name to optional<constant_info>, this mapping is faster than the one
       at environment. Moreover, it takes into account constant reducibility annotations.
       We have four different modes.
       - All (everything is transparent).
       - Semireducible (semireducible and reducible constants are considered transparent).
       - Instances (instances and reducible constants are considered transparent).
       - Reducible (only reducible constants are considered transparent).
       - None (everything is opaque).

       \remark In Semireducible, Instances and Reducible modes, projections and theorems are considered
       opaque independently of annotations. Actually, theorems will not be treated as opaque
       IF option `type_context_old.unfold_lemmas` is set to true.
       In All mode, projections are still considered opaque,
       this is not a problem since type_context_old implements a custom reduction rule for projections.

       The All mode is used for type inference where it is unacceptable to fail to infer a type.
       The Semireducible mode is used for scenarios where an `is_def_eq` is expected to succeed
       (e.g., exact and apply tactics).
       The Reducible mode (more restrictive) is used during search (e.g., type class resolution,
       simp, etc).
       The None mode is used when normalizing expressions without using delta-reduction. */
    transparency_cache            m_transparency_cache[LEAN_NUM_TRANSPARENCY_MODES];
    equiv_manager                 m_equiv_manager[LEAN_NUM_TRANSPARENCY_MODES];
    failure_cache                 m_failure_cache[LEAN_NUM_TRANSPARENCY_MODES];
    whnf_cache                    m_whnf_cache[LEAN_NUM_TRANSPARENCY_MODES];
    name2bool                     m_aux_recursor_cache;

    /* Cache datastructures for fun_info */

    typedef expr_map<fun_info>                fi_cache;
    typedef expr_unsigned_map<fun_info>       fi_cache_nargs;
    typedef expr_map<ss_param_infos>          ss_cache;
    typedef expr_unsigned_map<ss_param_infos> ss_cache_nargs;
    typedef expr_unsigned_map<unsigned>       prefix_cache;
    fi_cache                      m_fi_cache[LEAN_NUM_TRANSPARENCY_MODES];
    fi_cache_nargs                m_fi_cache_nargs[LEAN_NUM_TRANSPARENCY_MODES];
    ss_cache                      m_ss_cache[LEAN_NUM_TRANSPARENCY_MODES];
    ss_cache_nargs                m_ss_cache_nargs[LEAN_NUM_TRANSPARENCY_MODES];
    ss_cache_nargs                m_ss_cache_spec[LEAN_NUM_TRANSPARENCY_MODES];
    prefix_cache                  m_prefix_cache[LEAN_NUM_TRANSPARENCY_MODES];

public:
    context_cache();
    context_cache(options const & o);
    context_cache(context_cache const &) = delete;
    context_cache(context_cache &&) = default;
    virtual ~context_cache();

    context_cache & operator=(context_cache const &) = delete;
    context_cache & operator=(context_cache &&) = default;

    virtual optional<constant_info> get_decl(type_context_old &, transparency_mode, name const &) override;
    virtual optional<projection_info> get_proj_info(type_context_old &, name const &) override;
    virtual bool get_aux_recursor(type_context_old &, name const &) override;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) override;
    virtual void set_infer(expr const &, expr const &) override;

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) override;
    virtual void set_equiv(transparency_mode, expr const &, expr const &) override;

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;

    virtual optional<expr> get_whnf(transparency_mode, expr const &) override;
    virtual void set_whnf(transparency_mode, expr const &, expr const &) override;

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) override;
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) override;

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) override;

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) override;
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) override;

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) override;
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) override;

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override;

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override;
};
}
