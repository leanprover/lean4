/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/unique_id.h"
#include "library/abstract_context_cache.h"

namespace lean {
class context_cache;
typedef unique_id context_cache_id;

/*
   Ideally, we could have a "functional" implementation of abstract_context_cache using rb_map and rb_tree.
   This "functional" implementation could be used to store the cache, for example, in tactic_state objects.
   We don't use this solution for two reasons:
   - rb_map (and rb_tree) are 10x slower than hashtable maps (and sets).
   - The functional object would increase the size of the tactic_state object considerably.

   This class provides an alternative implementation where the tactic_state stores only the cache id.
   This id is used to retrieve a thread local context_cache object.
   See comment at abstract_context_cache for more details.
*/
class persistent_context_cache : public abstract_context_cache {
    context_cache_id                        m_id;
    std::unique_ptr<abstract_context_cache> m_cache_ptr;
public:
    persistent_context_cache(context_cache_id, options const &);
    virtual ~persistent_context_cache();

    context_cache_id get_id() const { return m_id; }

    /* Cached configuration options */
    virtual options const & get_options() const override;
    virtual bool get_unfold_lemmas() const override;
    virtual unsigned get_nat_offset_cnstr_threshold() const override;
    virtual unsigned get_smart_unfolding() const override;
    virtual unsigned get_class_instance_max_depth() const override;

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) override;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) override;
    virtual bool get_aux_recursor(type_context_old &, name const &) override;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) override;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) override;
    virtual void set_infer(expr const &, expr const &) override;

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) override;
    virtual void set_equiv(transparency_mode, expr const &, expr const &) override;

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;

    virtual optional<expr> get_whnf(transparency_mode, expr const &) override;
    virtual void set_whnf(transparency_mode, expr const &, expr const &) override;

    virtual optional<optional<expr>> get_instance(expr const &) override;
    virtual void set_instance(expr const &, optional<expr> const &) override;

    virtual optional<optional<expr>> get_subsingleton(expr const &) override;
    virtual void set_subsingleton(expr const &, optional<expr> const &) override;

    /* this method should flush the instance and subsingleton cache */
    virtual void flush_instances() override;

    virtual void reset_frozen_local_instances() override;
    virtual void set_frozen_local_instances(local_instances const & lis) override;
    virtual optional<local_instances> get_frozen_local_instances() const override;

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

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(expr const &, unsigned) override;
    virtual void set_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(expr const &, unsigned) override;
    virtual void set_specialized_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_congr_lemma(expr const &, unsigned) override;
    virtual void set_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_specialized_congr_lemma(expr const &, unsigned) override;
    virtual void set_specialized_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_hcongr_lemma(expr const &, unsigned) override;
    virtual void set_hcongr_lemma(expr const &, unsigned, congr_lemma const &) override;

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(expr const &, unsigned) override;
    virtual void set_app_builder_info(expr const &, unsigned, app_builder_info const &) override;

    virtual optional<app_builder_info> get_app_builder_info(expr const &, list<bool> const &) override;
    virtual void set_app_builder_info(expr const &, list<bool> const &, app_builder_info const &) override;
};
}
