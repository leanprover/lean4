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

namespace lean {
#define LEAN_NUM_TRANSPARENCY_MODES 5
enum class transparency_mode { All = 0, Semireducible, Instances, Reducible, None };

class type_context;

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
   type_context, app_builder, fun_info and congr_lemma.
   In the type_context, we cache inferred types, whnf, type class instances,
   to cite a few.

   This class do not implement any cache, only its interface. All operations
   do nothing.

   This class has been added to address problems with the former `type_context_cache_manager`.
   The `type_context_cache_manager` objects were stored in thread local objects.
   The correctness of this cache relied on the fact we used to never reuse fresh names in the whole system.
   This is not true in the new name_generator refactoring (for addressing issue #1601).
   The caches for the modules app_builder, congr_lemma and fun_info have the same problem.

   We have implemented a thread local cache reset operation, but it is
   not sufficient for fixing this issue since we only reset the cache
   before each command and when start a task.

   Here is a scenario that demonstrates the problem.
   Suppose we are executing the tactic `t1 <|> t2`.
   First, we execute `t1`, and in the process, the type_context
   cache is populated with new local constants created by `t1`.
   Then `t1` fails and we execute `t2`. When, we execute `t2`
   on the initial `tactic_state` object. Thus,
   `t2` may potentially create new local constants using the names
   used by `t1`, but with different types. So, the content
   of the cache is invalid.

   Here are possible implementations of this API:

   - An "imperative" implementation using hashtables, and it is useful for modules
     that own a type_context object (e.g., elaborator).
     This implementation is also useful for the new type_context API we are going to expose in the `io` monad.

   - In principle, a "functional" implementation using rb_map and rb_tree is possible.
     Then, this version could be stored in the tactic_state or local_context objects.
     We decided to not use it for performe issues. See comment above.

   - For caching contextual information in the tactic framework, we use the following approach:
     * We implement a thread local unique token generator.
     * The token can be viewed as a reference to the cache.
     * tactic_state stores this token.
     * Thread local storage stores the "imperative" implementation and a token of its owner.
     * When we create a type_context for a tactic_state we check whether the thread local
       storage contains the cache for the given tactic_state. If yes, we use it, and obtain
       a new token for it since we will perform destructive updates.
       Otherwise, we create a new one.
     * When we finish using the type_context, we update the tactic_state with the new fresh token,
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
          elaborate its body. The freeze step is also useful to speedup the type_context initialization
          (see comment in the type_context class). So, we just check if the frozen local instances are the same
          before starting each step. This check is performed in the method `init_local_instances`.

   Here are some benefits of the new approach:

   - The cache will be smaller in many cases. For example, after `t1` fails in `t1 <|> t2`, the cached information
     about its new fresh local constants is not useful anymore, but it stays in the current
     cache.

   - We don't need to check whether the cache is valid or not when we create a new
     type_context.

   - It is more efficient when creating temporary type_context objects for performing
     a single operation. In this kind of scenario, we can use the dummy cache implementation
     that doesn't cache anything.

   - It is easy to experiment with new cache data structures.

   - We can easily flush the cache if a primitive tactic performs an operation that invalidates it.
     Examples:
     * A tactic that allows user to use all local class instances available in the local context.
     * A tactic that reverses local instances
*/
class context_cache {
protected:
    options                   m_options;
    bool                      m_unfold_lemmas;
    unsigned                  m_nat_offset_cnstr_threshold;
    unsigned                  m_smart_unfolding;
    unsigned                  m_class_instance_max_depth;
    optional<local_instances> m_local_instances;
    bool is_transparent(type_context & ctx, transparency_mode m, declaration const & d);
public:
    context_cache();
    context_cache(options const &);
    /* Create a "dummy" context_cache with the same configuration options.
       The bool parameter is not used. It is here just to make sure we don't confuse
       this constructor with the copy constructor. */
    context_cache(context_cache const &, bool);
    context_cache(context_cache const &) = delete;
    context_cache(context_cache &&) = default;
    virtual ~context_cache() {}

    context_cache & operator=(context_cache const &) = delete;
    context_cache & operator=(context_cache &&) = default;

    /* Cached configuration options */
    options const & get_options() const { return m_options; }
    bool get_unfold_lemmas() const { return m_unfold_lemmas; }
    unsigned get_nat_offset_cnstr_threshold() const { return m_nat_offset_cnstr_threshold; }
    unsigned get_smart_unfolding() const { return m_smart_unfolding; }
    unsigned get_class_instance_max_depth() const { return m_class_instance_max_depth; }

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context &, transparency_mode, name const &);
    virtual projection_info const * get_proj_info(type_context &, name const &);
    virtual bool get_aux_recursor(type_context &, name const &);

    /* Cache support for type_context module */

    virtual optional<expr> get_infer(type_context &, expr const &) { return none_expr(); }
    virtual void set_infer(type_context &, expr const &, expr const &) {}

    virtual bool get_equiv(type_context &, expr const &, expr const &) { return false; }
    virtual void set_equiv(type_context &, expr const &, expr const &) {}

    virtual bool get_is_def_eq_failure(type_context &, expr const &, expr const &) { return false; }
    virtual void set_is_def_eq_failure(type_context &, expr const &, expr const &) {}

    virtual optional<expr> get_whnf(type_context &, expr const &) { return none_expr(); }
    virtual void set_whnf(type_context &, expr const &, expr const &) {}

    virtual optional<optional<expr>> get_instance(type_context &, expr const &) { return optional<optional<expr>>(); }
    virtual void set_instance(type_context &, expr const &, optional<expr> const &) {}

    virtual optional<optional<expr>> get_subsingleton(type_context &, expr const &) { return optional<optional<expr>>(); }
    virtual void set_subsingleton(type_context &, expr const &, optional<expr> const &) {}

    /* this method should flush the instance and subsingleton cache */
    virtual void flush_instances() {}

    void reset_frozen_local_instances() { m_local_instances = optional<local_instances>(); }
    void set_frozen_local_instances(local_instances const & lis) { m_local_instances = lis; }
    optional<local_instances> get_frozen_local_instances() const { return m_local_instances; }

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(type_context &, expr const &) { return optional<fun_info>(); }
    virtual void set_fun_info(type_context &, expr const &, fun_info const &) {}

    virtual optional<fun_info> get_fun_info_nargs(type_context &, expr const &, unsigned) { return optional<fun_info>(); }
    virtual void set_fun_info_nargs(type_context &, expr const &, unsigned, fun_info const &) {}

    virtual optional<unsigned> get_specialization_prefix_size(type_context &, expr const &, unsigned) { return optional<unsigned>(); }
    virtual void set_specialization_prefix_size(type_context &, expr const &, unsigned, unsigned) {}

    virtual optional<ss_param_infos> get_subsingleton_info(type_context &, expr const &) { return optional<ss_param_infos>(); }
    virtual void set_subsingleton_info(type_context &, expr const &, ss_param_infos const &) {}

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(type_context &, expr const &, unsigned) { return optional<ss_param_infos>(); }
    virtual void set_subsingleton_info_nargs(type_context &, expr const &, unsigned, ss_param_infos const &) {}

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(type_context &, expr const &, unsigned) { return optional<ss_param_infos>(); }
    virtual void set_specialization_subsingleton_info_nargs(type_context &, expr const &, unsigned, ss_param_infos const &) {}

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(type_context &, expr const &, unsigned) { return optional<congr_lemma>(); }
    virtual void set_simp_congr_lemma(type_context &, expr const &, unsigned, congr_lemma const &) {}

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(type_context &, expr const &, unsigned) { return optional<congr_lemma>(); }
    virtual void set_specialized_simp_congr_lemma(type_context &, expr const &, unsigned, congr_lemma const &) {}

    virtual optional<congr_lemma> get_congr_lemma(type_context &, expr const &, unsigned) { return optional<congr_lemma>(); }
    virtual void set_congr_lemma(type_context &, expr const &, unsigned, congr_lemma const &) {}

    virtual optional<congr_lemma> get_specialized_congr_lemma(type_context &, expr const &, unsigned) { return optional<congr_lemma>(); }
    virtual void set_specialized_congr_lemma(type_context &, expr const &, unsigned, congr_lemma const &) {}

    virtual optional<congr_lemma> get_hcongr_lemma(type_context &, expr const &, unsigned) { return optional<congr_lemma>(); }
    virtual void set_hcongr_lemma(type_context &, expr const &, unsigned, congr_lemma const &) {}

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(type_context &, expr const &, unsigned) { return optional<app_builder_info>(); }
    virtual void set_app_builder_info(type_context &, expr const &, unsigned, app_builder_info const &) {}

    virtual optional<app_builder_info> get_app_builder_info(type_context &, expr const &, list<bool> const &) { return optional<app_builder_info>(); }
    virtual void set_app_builder_info(type_context &, expr const &, list<bool> const &, app_builder_info const &) {}
};

void initialize_context_cache();
void finalize_context_cache();
}
