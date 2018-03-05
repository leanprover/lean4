/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lbool.h"
#include "kernel/expr.h"
#include "kernel/declaration.h"
#include "library/congr_lemma.h"
#include "library/projection.h"
#include "library/fun_info.h"
#include "library/local_instances.h"
#include "library/unification_hint.h"

namespace lean {
#define LEAN_NUM_TRANSPARENCY_MODES 5
enum class transparency_mode { All = 0, Semireducible, Instances, Reducible, None };

class type_context_old;

/* Auxiliary information that is cached by the app_builder module in
   the context_cache. */
struct app_builder_info {
    unsigned             m_num_umeta;
    unsigned             m_num_emeta;
    expr                 m_app;
    list<optional<expr>> m_inst_args; // "mask" of implicit instance arguments
    list<expr>           m_expl_args; // metavars for explicit arguments
    /*
      IMPORTANT: for m_inst_args we store the arguments in reverse order.
      For example, the first element in the list indicates whether the last argument
      is an instance implicit argument or not. If it is not none, then the element
      is the associated metavariable

      m_expl_args are also stored in reverse order
    */
};

/*
   We have two main kinds of cache in Lean: environmental and contextual.
   The environmental caches only depend on the environment, and are easier to maintain.
   We usually store them in thread local storage, and before using them we compare
   if the current environment is a descendant of the one in the cache, and we
   check for attribute fingerprints.

   This class defines the interface for contextual caches.
   A contextual cache depends on the local_context object.
   Ideally, the cache should be stored in the local_context object,
   but this is not feasible due to performance issues. The local_context object
   should support a fast O(1) copy operation. Thus, we implement it using
   functional data-structures such as red-black trees. This kind of data-structure
   is too inefficient for a cache data structure, and we want to be able to
   use hashtables (at least 10x faster than red-black trees). Another
   issue is that we want to keep the `local_context` object simple and
   without the overhead of many caches.

   We use contextual caches for the operations performed in the following modules:
   type_context_old, app_builder, fun_info and congr_lemma.
   In the type_context_old, we cache inferred types, whnf, type class instances,
   to cite a few.

   This class has been added to address problems with the former `type_context_old_cache_manager`.
   The `type_context_old_cache_manager` objects were stored in thread local objects.
   The correctness of this cache relied on the fact we used to never reuse fresh names in the whole system.
   This is not true in the new name_generator refactoring (for addressing issue #1601).
   The caches for the modules app_builder, congr_lemma and fun_info have the same problem.

   We have implemented a thread local cache reset operation, but it is
   not sufficient for fixing this issue since we only reset the cache
   before each command and when start a task.

   Here is a scenario that demonstrates the problem.
   Suppose we are executing the tactic `t1 <|> t2`.
   First, we execute `t1`, and in the process, the type_context_old
   cache is populated with new local constants created by `t1`.
   Then `t1` fails and we execute `t2`. When, we execute `t2`
   on the initial `tactic_state` object. Thus,
   `t2` may potentially create new local constants using the names
   used by `t1`, but with different types. So, the content
   of the cache is invalid.

   Here are possible implementations of this API:

   - An "imperative" implementation using hashtables, and it is useful for modules
     that own a type_context_old object (e.g., elaborator).
     This implementation is also useful for the new type_context_old API we are going to expose in the `io` monad.

   - In principle, a "functional" implementation using rb_map and rb_tree is possible.
     Then, this version could be stored in the tactic_state or local_context objects.
     We decided to not use it for performe issues. See comment above.

   - For caching contextual information in the tactic framework, we use the following approach:
     * We implement a thread local unique token generator.
     * The token can be viewed as a reference to the cache.
     * tactic_state stores this token.
     * Thread local storage stores the "imperative" implementation and a token of its owner.
     * When we create a type_context_old for a tactic_state we check whether the thread local
       storage contains the cache for the given tactic_state. If yes, we use it, and obtain
       a new token for it since we will perform destructive updates.
       Otherwise, we create a new one.
     * When we finish using the type_context_old, we update the tactic_state with the new fresh token,
       and put the updated cache back into the thread local storage.

       Remark: the thread local storage may store more than one cache.

       Remark: this approach should work well for "sequential" tactic execution.
          For `t1 <|> t2`, if `t1` fails, `t2` will potentially start with the empty cache
          since the thread local storage contains the cache for `t1`.
          We should measure whether this approach is more efficient than the functional one.
          With the "abstract interface", we can even have both approaches.

       Remark: we have considered storing the token on the local context, but this is not ideal
       because there are many tactics that create more than on subgoal (e.g., `apply`),
       and we would have to use an empty cache for each subgoal but the first.
       The situation would be analogous to the `t1 <|> t2` scenario described in the previous
       remark. Moreover, the different subgoals usually have very similar local contexts
       and information cached in one can be reused in the others.

       Remark: recall that in a sequence of tactic_states [s_1, s_2, ...] obtained by executing tactics [t_1, t_2, ...]

            s_1 -t_1-> s_2 -t_2-> s_3 -> ...

       we never reuse names for labeling local declarations, and the cache is reused, since we will store the
       cache on the thread local storage after each step, and will retrieve it before the beginning of the following step.
       Most cached data (e.g., inferred types) is still valid because we never reuse names in the sequence.
       The only exception is cached data related to type class instances and subsigletons (which depends on type class instances).
       Here the result depends on the local instances available in the local context.
       Recall we have two modes for handling local instances:

       1) liberal: any local instance can be used. In this mode, the cache for type class instances and subsigletons has to be
          flushed in the beginning of each step if the local_context is different from the previous one. Actually,
          we do not track the local_context. So, the cache is always flushed in the beginning of each step in the liberal mode.
          This is fine because we only use the "liberal" mode when elaborating the header of a declaration.

       2) frozen: after elaborating the header of a declaration, we freeze the local instances that can be used to
          elaborate its body. The freeze step is also useful to speedup the type_context_old initialization
          (see comment in the type_context_old class). So, we just check if the frozen local instances are the same
          before starting each step. This check is performed in the method `init_local_instances`.

   Here are some benefits of the new approach:

   - The cache will be smaller in many cases. For example, after `t1` fails in `t1 <|> t2`, the cached information
     about its new fresh local constants is not useful anymore, but it stays in the current
     cache.

   - We don't need to check whether the cache is valid or not when we create a new
     type_context_old.

   - It is more efficient when creating temporary type_context_old objects for performing
     a single operation. In this kind of scenario, we can use the dummy cache implementation
     that doesn't cache anything.

   - It is easy to experiment with new cache data structures.

   - We can easily flush the cache if a primitive tactic performs an operation that invalidates it.
     Examples:
     * A tactic that allows user to use all local class instances available in the local context.
     * A tactic that reverses local instances
*/
class abstract_context_cache {
public:
    abstract_context_cache() {}
    abstract_context_cache(abstract_context_cache const &) = delete;
    abstract_context_cache(abstract_context_cache &&) = default;
    virtual ~abstract_context_cache() {}

    abstract_context_cache & operator=(abstract_context_cache const &) = delete;
    abstract_context_cache & operator=(abstract_context_cache &&) = default;

    /* Cached configuration options */
    virtual options const & get_options() const = 0;
    virtual bool get_unfold_lemmas() const = 0;
    virtual unsigned get_nat_offset_cnstr_threshold() const = 0;
    virtual unsigned get_smart_unfolding() const = 0;
    virtual unsigned get_class_instance_max_depth() const = 0;

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) = 0;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) = 0;
    virtual bool get_aux_recursor(type_context_old &, name const &) = 0;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) = 0;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) = 0;
    virtual void set_infer(expr const &, expr const &) = 0;

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) = 0;
    virtual void set_equiv(transparency_mode, expr const &, expr const &) = 0;

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) = 0;
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) = 0;

    virtual optional<expr> get_whnf(transparency_mode, expr const &) = 0;
    virtual void set_whnf(transparency_mode, expr const &, expr const &) = 0;

    virtual optional<optional<expr>> get_instance(expr const &) = 0;
    virtual void set_instance(expr const &, optional<expr> const &) = 0;

    virtual optional<optional<expr>> get_subsingleton(expr const &) = 0;
    virtual void set_subsingleton(expr const &, optional<expr> const &) = 0;

    /* this method should flush the instance and subsingleton cache */
    virtual void flush_instances() = 0;

    virtual void reset_frozen_local_instances() = 0;
    virtual void set_frozen_local_instances(local_instances const & lis) = 0;
    virtual optional<local_instances> get_frozen_local_instances() const = 0;

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) = 0;
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) = 0;

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) = 0;

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) = 0;

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) = 0;
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) = 0;

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) = 0;

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) = 0;

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_specialized_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_specialized_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_specialized_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_hcongr_lemma(expr const &, unsigned) = 0;
    virtual void set_hcongr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(expr const &, unsigned) = 0;
    virtual void set_app_builder_info(expr const &, unsigned, app_builder_info const &) = 0;

    virtual optional<app_builder_info> get_app_builder_info(expr const &, list<bool> const &) = 0;
    virtual void set_app_builder_info(expr const &, list<bool> const &, app_builder_info const &) = 0;
};

/* Dummy implementation of the abstract_context_cache interface that does not do cache anything but configuration options. */
class context_cacheless : public abstract_context_cache {
protected:
    bool is_transparent(type_context_old & ctx, transparency_mode m, declaration const & d);
private:
    options                   m_options;
    bool                      m_unfold_lemmas;
    unsigned                  m_nat_offset_cnstr_threshold;
    unsigned                  m_smart_unfolding;
    unsigned                  m_class_instance_max_depth;
    optional<local_instances> m_local_instances;
public:
    context_cacheless();
    context_cacheless(options const &);
    /* Faster version of `context_cacheless(c.get_options())`.
       The bool parameter is not used. It is here just to make sure we don't confuse
       this constructor with the copy constructor. */
    context_cacheless(abstract_context_cache const &, bool);
    context_cacheless(context_cacheless const &) = delete;
    context_cacheless(context_cacheless &&) = default;
    virtual ~context_cacheless() {}

    context_cacheless & operator=(context_cacheless const &) = delete;
    context_cacheless & operator=(context_cacheless &&) = default;

    virtual options const & get_options() const override { return m_options; }
    virtual bool get_unfold_lemmas() const override { return m_unfold_lemmas; }
    virtual unsigned get_nat_offset_cnstr_threshold() const override  { return m_nat_offset_cnstr_threshold; }
    virtual unsigned get_smart_unfolding() const override  { return m_smart_unfolding; }
    virtual unsigned get_class_instance_max_depth() const override  { return m_class_instance_max_depth; }

    virtual void reset_frozen_local_instances() override { m_local_instances = optional<local_instances>(); }
    virtual void set_frozen_local_instances(local_instances const & lis) override { m_local_instances = lis; }
    virtual optional<local_instances> get_frozen_local_instances() const override { return m_local_instances; }

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) override;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) override;
    virtual bool get_aux_recursor(type_context_old &, name const &) override;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) override;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) override { return none_expr(); }
    virtual void set_infer(expr const &, expr const &) override {}

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) override { return false; }
    virtual void set_equiv(transparency_mode, expr const &, expr const &) override {}

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) override { return false; }
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) override {}

    virtual optional<expr> get_whnf(transparency_mode, expr const &) override { return none_expr(); }
    virtual void set_whnf(transparency_mode, expr const &, expr const &) override {}

    virtual optional<optional<expr>> get_instance(expr const &) override { return optional<optional<expr>>(); }
    virtual void set_instance(expr const &, optional<expr> const &) override {}

    virtual optional<optional<expr>> get_subsingleton(expr const &) override { return optional<optional<expr>>(); }
    virtual void set_subsingleton(expr const &, optional<expr> const &) override {}

    virtual void flush_instances() override {}

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) override { return optional<fun_info>(); }
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) override {}

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) override { return optional<fun_info>(); }
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) override {}

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) override { return optional<unsigned>(); }
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) override {}

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) override { return optional<ss_param_infos>(); }
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) override {}

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override { return optional<ss_param_infos>(); }
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override {}

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override { return optional<ss_param_infos>(); }
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override {}

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_specialized_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_specialized_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_specialized_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_hcongr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_hcongr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(expr const &, unsigned) override { return optional<app_builder_info>(); }
    virtual void set_app_builder_info(expr const &, unsigned, app_builder_info const &) override {}

    virtual optional<app_builder_info> get_app_builder_info(expr const &, list<bool> const &) override { return optional<app_builder_info>(); }
    virtual void set_app_builder_info(expr const &, list<bool> const &, app_builder_info const &) override {}
};

void initialize_abstract_context_cache();
void finalize_abstract_context_cache();
}
