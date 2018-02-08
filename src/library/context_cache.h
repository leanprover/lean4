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

namespace lean {
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

/* Cache for type_context, app_builder, fun_info and congr_lemma.

   The default implementation does nothing.

   This class has been added to address problems with the former `type_context_cache_manager`.
   The `type_context_cache_manager` objects were stored in thread local objects.
   The correctness of this cache relied on the fact we never reuse fresh names.
   This is not true in the new name_generator refactoring (for addressing issue #1601).
   The caches for the modules app_builder, congr_lemma and fun_info have the same problem.

   We have implemented a thread local cache reset operation, but it is
   not sufficient for fixing this issue since we only reset the cache
   before each command and when start a task.

   Here is a scenario that demonstrates the problem.
   Suppose we are executing the tactic `t1 <|> t2`.
   First, we execute `t1`, and in the process, the type_context
   cache is populated with new local constants created by `t1`.
   Then `t1` fails and we execute `t2`. After the refactoring,
   the tactic_state contains a name_generator. So, `t2` may
   potentially create new local constants using the names
   used by `t2`, but with different types. So, the content
   of the cache is invalid.

   Thus, we decided to add this abstract class (aka interface) for the caching operations
   performed by the following modules: type_context, congr_lemma, app_builder and fun_info.

   Here are possible implementations of this API:

   - An "imperative" implementation using hashtables, and it is useful for modules
     that own a type_context object (e.g., elaborator).
     This implementation is also useful for the new type_context API we are going to expose in the `io` monad.

   - A "functional" implementation using rb_map and rb_tree.
     This cache can be stored in the tactic_state. Remark: we do not need
     to implement the whole interface, only the most important caches (e.g., the one for type inference).

   - If functional data structures are too inefficient. We can use the following alternative design:
     * We implement a thread local unique token generator.
     * The token can be viewed as a reference to the cache.
     * tactic_state stores its token.
     * Thread local storage stores the "imperative" implementation and a token of its owner.
     * When we create a type_context for a tactic_state we check whether the thread local
       storage contains the cache for the given tactic_state. If yes, we use it. Otherwise,
       we create a new one.
     * When we finish using the type_context, we update the tactic_state with a fresh token,
       and put the updated cache back into the thread local storage.

       Remark: the thread local storage may store more than one cache.
       Remark: this approach should work well for "sequential" tactic execution.
          For `t1 <|> t2`, if `t1` fails, `t2` will potentially start with the empty cache
          since the thread local storage contains the cache for `t1`.
          We should measure whether this approach is more efficient than the functional one.
          With the "abstract interface", we can even have both approaches.

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
public:
    /* Cache support for type_context module */

    virtual optional<expr> get_infer(type_context &, expr const &) { return none_expr(); }
    virtual void set_infer(type_context &, expr const &, expr const &) {}

    virtual optional<projection_info> get_proj_info(type_context &, name const &) { return optional<projection_info>(); }
    virtual void set_proj_info(type_context &, name const &, projection_info const &) {}

    virtual bool get_equiv(type_context &, expr const &, expr const &) { return false; }
    virtual void set_equiv(type_context &, expr const &, expr const &) {}

    virtual bool get_is_def_eq_failure(type_context &, expr const &, expr const &) { return false; }
    virtual void set_is_def_eq_failure(type_context &, expr const &, expr const &) {}

    virtual lbool get_aux_recursor(type_context &, name const &) { return l_undef; }
    virtual void set_aux_recursor(type_context &, name const &, bool) {}

    virtual optional<declaration> get_decl(type_context &, name const &) { return optional<declaration>(); }
    virtual void set_decl(type_context &, name const &, optional<declaration> const &) {}

    virtual optional<expr> get_whnf(type_context &, expr const &) { return none_expr(); }
    virtual void set_whnf(type_context &, expr const &, expr const &) {}

    virtual optional<expr> get_instance(type_context &, expr const &) { return none_expr(); }
    virtual void set_instance(type_context &, expr const &, expr const &) {}

    virtual optional<expr> get_subsingleton(type_context &, expr const &) { return none_expr(); }
    virtual void set_subsingleton(type_context &, expr const &, expr const &) {}

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
}
